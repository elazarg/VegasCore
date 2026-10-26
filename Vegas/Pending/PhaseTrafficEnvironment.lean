/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseTraffic
import Vegas.Pending.PhaseProposalShadowEnvironment

/-! # Exact phase command laws with hidden private binding meanings

The actual native command kernels and phase normalizer preserve focal traffic
when completed foreign binding meanings are represented by the existing
private binding frame. Clock, chance and expiry share their actual draws;
retry may change the frame's logical mask while retaining full public archives.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

/-- The actual physical command admits a joint coupling retaining its dynamic
private frame, so a later command may use the resulting compatibility witness. -/
theorem PhaseStateFrame.environment_coupling {memory : BindingShadow graph}
    {hidden : Player} {left right : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory hidden left right) (owned : memory.OwnBindings hidden)
    (supported : memory.CompletedAt right.current.native.config)
    (runtime : EventGraphRuntime graph) (command : EnvironmentCommand graph) :
    ∃ joint : PMF (PhaseRuntimeState graph × PhaseRuntimeState graph),
      joint.map Prod.fst = left.environment runtime command ∧
      joint.map Prod.snd = right.environment runtime command ∧
      ∀ pair ∈ joint.support, ∃ next : BindingShadow graph,
        next.OwnBindings hidden ∧ next.candidates = memory.candidates ∧
        PhaseStateFrame next hidden pair.1 pair.2 ∧
        next.CompletedAt pair.2.current.native.config := by
  have allowedEq : left.commandAllowed command = right.commandAllowed command := by
    cases command <;> simp only [PhaseRuntimeState.commandAllowed, frame.phases]
  cases allowed : left.commandAllowed command with
  | false =>
    have rightAllowed := allowedEq.symm.trans allowed
    refine ⟨PMF.pure (left, right), ?_, ?_, ?_⟩
    · simp only [PMF.pure_map, PhaseRuntimeState.environment, allowed, Bool.false_eq_true,
        ite_false]
    · simp only [PMF.pure_map, PhaseRuntimeState.environment, rightAllowed, Bool.false_eq_true,
        ite_false]
    · intro pair present
      cases (PMF.mem_support_pure_iff _ _).mp present
      exact ⟨memory, owned, rfl, frame, supported⟩
  | true =>
    have rightAllowed := allowedEq.symm.trans allowed
    let first := fun native : State graph =>
      ({ left with current :=
        left.current.environmentResult command (memory.native hidden native) } :
        PhaseRuntimeState graph).normalize
    let second := fun native : State graph =>
      ({ right with current := right.current.environmentResult command native } :
        PhaseRuntimeState graph).normalize
    let joint := (environmentStep runtime right.current.native command).map fun native =>
      (first native, second native)
    have nativeEq : left.current.native = memory.native hidden right.current.native := by
      rw [frame.current]
      rfl
    refine ⟨joint, ?_, ?_, ?_⟩
    · simp only [joint, PMF.map_comp, Function.comp_def, PhaseRuntimeState.environment,
        allowed, ite_true]
      rw [nativeEq, native_environment memory hidden owned runtime right.current.native supported
        command, PMF.map_comp]
      rfl
    · simp only [joint, PMF.map_comp, Function.comp_def, PhaseRuntimeState.environment,
        rightAllowed, ite_true]
      rfl
    · intro pair present
      obtain ⟨native, moved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp present
      let firstRaw : PhaseRuntimeState graph :=
        { left with current :=
          left.current.environmentResult command (memory.native hidden native) }
      let secondRaw : PhaseRuntimeState graph :=
        { right with current := right.current.environmentResult command native }
      have current : firstRaw.current = memory.recovery hidden secondRaw.current := by
        dsimp only [firstRaw, secondRaw]
        rw [frame.current]
        cases command <;> rfl
      have rawFrame : PhaseStateFrame memory hidden firstRaw secondRaw :=
        ⟨frame.phases, frame.generation, frame.entry, current, frame.retired⟩
      have rawSupport : memory.CompletedAt secondRaw.current.native.config := by
        intro event stored
        exact environmentStep_completed_subset runtime right.current.native native command moved
          (supported event stored)
      obtain ⟨next, nextOwned, candidates, paired, support, _refinement⟩ :=
        rawFrame.normalize owned rawSupport
      exact ⟨next, nextOwned, candidates, paired, support⟩


/-- A concrete private-binding frame induces equality of the entire focal
application-view law through every actual physical application command. -/
theorem PhaseStateFrame.environment_playerView_law {memory : BindingShadow graph}
    {hidden : Player} {left right : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory hidden left right) (owned : memory.OwnBindings hidden)
    (supported : memory.CompletedAt right.current.native.config)
    (runtime : EventGraphRuntime graph) (focal : Player) (different : focal ≠ hidden)
    (command : EnvironmentCommand graph) :
    ((left.environment runtime command).map fun next => next.playerView focal) =
      ((right.environment runtime command).map fun next => next.playerView focal) := by
  obtain ⟨joint, firstLaw, secondLaw, compatible⟩ :=
    frame.environment_coupling owned supported runtime command
  rw [← firstLaw, ← secondLaw, PMF.map_comp, PMF.map_comp]
  apply map_congr_on_support _
  intro pair present
  obtain ⟨next, nextOwned, _candidates, paired, _support⟩ := compatible pair present
  exact paired.playerView_other nextOwned focal different

end BindingShadow

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Couple the complete actual application-command kernels while retaining
both focal traffic and the successor private frame at every coupled outcome. -/
theorem phaseTraffic_application_coupling {memory : BindingShadow graph} {hidden : Player}
    (left right : (app).Execution)
    (frame : memory.PhaseStateFrame hidden left.application right.application)
    (owned : memory.OwnBindings hidden)
    (supported : memory.CompletedAt right.application.current.native.config)
    (focal : Player) (different : focal ≠ hidden)
    (same : phaseTraffic runtime leaks focal left = phaseTraffic runtime leaks focal right)
    (command : EnvironmentCommand graph) :
    ∃ joint : PMF ((app).Execution × (app).Execution),
      joint.map Prod.fst = left.environmentStep (app) (.application command) ∧
      joint.map Prod.snd = right.environmentStep (app) (.application command) ∧
      ∀ pair ∈ joint.support,
        phaseTraffic runtime leaks focal pair.1 = phaseTraffic runtime leaks focal pair.2 ∧
        ∃ next : BindingShadow graph,
          next.OwnBindings hidden ∧ next.candidates = memory.candidates ∧
          next.PhaseStateFrame hidden pair.1.application pair.2.application ∧
          next.CompletedAt pair.2.application.current.native.config := by
  have network : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have before : left.observeEnvironment (app) = right.observeEnvironment (app) := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, frame.publicView owned]
    rfl
  obtain ⟨states, firstLaw, secondLaw, compatible⟩ :=
    frame.environment_coupling owned supported runtime command
  let first := fun state : PhaseRuntimeState graph =>
    ({ left with application := state, environmentRecall := left.environmentRecall ++
      [⟨left.observeEnvironment (app), .application command⟩] } : (app).Execution)
  let second := fun state : PhaseRuntimeState graph =>
    ({ right with application := state, environmentRecall := right.environmentRecall ++
      [⟨right.observeEnvironment (app), .application command⟩] } : (app).Execution)
  let joint := states.map fun pair => (first pair.1, second pair.2)
  refine ⟨joint, ?_, ?_, ?_⟩
  · change (states.map fun pair => (first pair.1, second pair.2)).map Prod.fst = _
    rw [PMF.map_comp]
    change states.map (first ∘ Prod.fst) = _
    rw [← PMF.map_comp, firstLaw]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp, Function.comp_def,
      first, phaseApplication]
  · change (states.map fun pair => (first pair.1, second pair.2)).map Prod.snd = _
    rw [PMF.map_comp]
    change states.map (second ∘ Prod.snd) = _
    rw [← PMF.map_comp, secondLaw]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp, Function.comp_def,
      second, phaseApplication]
  · intro pair present
    obtain ⟨sourcePair, sourceSupported, pairEq⟩ :=
      (PMF.mem_support_map_iff (fun pair => (first pair.1, second pair.2)) states _).mp present
    subst pair
    obtain ⟨next, nextOwned, candidates, paired, support⟩ := compatible sourcePair sourceSupported
    refine ⟨?_, next, nextOwned, candidates, paired, support⟩
    refine Prod.ext network (Prod.ext receipts (Prod.ext ?_ (Prod.ext recalled ?_)))
    · change left.environmentRecall ++ [⟨left.observeEnvironment (app), .application command⟩] =
        right.environmentRecall ++ [⟨right.observeEnvironment (app), .application command⟩]
      rw [before, environments]
    · exact paired.playerView_other nextOwned focal different


/-- The full focal communication readout has the same law through any
application command. The binding compatibility is structural, and the actual
clock, chance, expiry, rollback, archive and environment recall are retained. -/
theorem phaseTraffic_application_law {memory : BindingShadow graph} {hidden : Player}
    (left right : (app).Execution)
    (frame : BindingShadow.PhaseStateFrame memory hidden left.application right.application)
    (owned : memory.OwnBindings hidden)
    (supported : memory.CompletedAt right.application.current.native.config)
    (focal : Player) (different : focal ≠ hidden)
    (same : phaseTraffic runtime leaks focal left = phaseTraffic runtime leaks focal right)
    (command : EnvironmentCommand graph) :
    ((left.environmentStep (app) (.application command)).map (phaseTraffic runtime leaks focal)) =
      ((right.environmentStep (app) (.application command)).map
        (phaseTraffic runtime leaks focal)) := by
  obtain ⟨joint, firstLaw, secondLaw, compatible⟩ :=
    phaseTraffic_application_coupling runtime leaks left right frame owned supported focal
      different same command
  rw [← firstLaw, ← secondLaw, PMF.map_comp, PMF.map_comp]
  exact map_congr_on_support _ fun pair present => (compatible pair present).1

end Vegas.EventGraphRuntime
