/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowSample
import Vegas.Pending.PhaseProposalShadowExpiry
import Vegas.Pending.PhaseProposalShadowProgress

/-! # Original application-command outcomes construct repaired outcomes

All three native command laws are the owning operational laws. Public chance
uses the same draw; expiry uses the same entered clock and literal FALSE;
clock advancement changes no meanings. General recovery then selects its
actual output mask without imposing a clear state or an empty archive.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The exact native command law, including arbitrary public sample
distributions and actual overdue events. -/
theorem native_environment (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (runtime : EventGraphRuntime graph)
    (state : State graph) (supported : memory.CompletedAt state.config)
    (command : EnvironmentCommand graph) :
    environmentStep runtime (memory.native owner state) command =
      (environmentStep runtime state command).map (memory.native owner) := by
  cases command with
  | advanceClock => exact native_advanceClock memory owner runtime state
  | executeSample event => exact native_executeSample memory owner owned runtime state event
  | expire event => exact native_expire memory owner runtime state supported event

/-- A realized original outcome yields an actual repaired outcome. The
direction matters: the repaired transition is constructed from the original
draw rather than supplied as an extra hypothesis of the history repair. -/
theorem PhaseStateFrame.environment_repair {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory owner original repaired)
    (owned : memory.OwnBindings owner)
    (supported : memory.CompletedAt repaired.current.native.config)
    (runtime : EventGraphRuntime graph) (command : EnvironmentCommand graph)
    (next : PhaseRuntimeState graph)
    (reached : next ∈ (original.environment runtime command).support) :
    ∃ (nextMemory : BindingShadow graph) (image : PhaseRuntimeState graph),
      image ∈ (repaired.environment runtime command).support ∧
      nextMemory.OwnBindings owner ∧ nextMemory.candidates = memory.candidates ∧
      PhaseStateFrame nextMemory owner next image ∧
      nextMemory.CompletedAt image.current.native.config ∧
      (original.entry.native.config.store.BindingRefines repaired.entry.native.config.store →
        original.current.native.config.store.BindingRefines repaired.current.native.config.store →
        next.entry.native.config.store.BindingRefines image.entry.native.config.store ∧
        next.current.native.config.store.BindingRefines image.current.native.config.store) := by
  classical
  have allowedEq : original.commandAllowed command = repaired.commandAllowed command := by
    cases command <;> simp only [PhaseRuntimeState.commandAllowed, frame.phases]
  cases allowed : original.commandAllowed command with
  | false =>
      have rightAllowed := allowedEq.symm.trans allowed
      simp only [PhaseRuntimeState.environment, allowed, Bool.false_eq_true,
        ↓reduceIte, PMF.mem_support_pure_iff] at reached
      subst next
      refine ⟨memory, repaired, ?_, owned, rfl, frame, supported,
        fun entryRef currentRef => ⟨entryRef, currentRef⟩⟩
      simp only [PhaseRuntimeState.environment, rightAllowed, Bool.false_eq_true,
        ↓reduceIte, PMF.mem_support_pure_iff]
  | true =>
      have rightAllowed := allowedEq.symm.trans allowed
      simp only [PhaseRuntimeState.environment, allowed, ↓reduceIte] at reached
      obtain ⟨sourceNative, sourceMoved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      have transformed : sourceNative ∈
          ((environmentStep runtime repaired.current.native command).map
            (memory.native owner)).support := by
        rw [frame.current] at sourceMoved
        change sourceNative ∈
          (environmentStep runtime (memory.native owner repaired.current.native) command).support
            at sourceMoved
        rw [native_environment memory owner owned runtime repaired.current.native supported command]
          at sourceMoved
        exact sourceMoved
      obtain ⟨native, moved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp transformed
      let leftRaw : PhaseRuntimeState graph :=
        { original with
          current := original.current.environmentResult command (memory.native owner native) }
      let rightRaw : PhaseRuntimeState graph :=
        { repaired with current := repaired.current.environmentResult command native }
      have currentEq : leftRaw.current = memory.recovery owner rightRaw.current := by
        dsimp only [leftRaw, rightRaw]
        rw [frame.current]
        cases command <;> rfl
      have rawFrame : PhaseStateFrame memory owner leftRaw rightRaw :=
        ⟨frame.phases, frame.generation, frame.entry, currentEq, frame.retired⟩
      have rawSupport : memory.CompletedAt rightRaw.current.native.config := by
        intro prior present
        exact environmentStep_completed_subset runtime repaired.current.native native command moved
          (supported prior present)
      obtain ⟨nextMemory, nextOwned, candidates, paired, nextSupport, refineStores⟩ :=
        rawFrame.normalize owned rawSupport
      have rawRefinement
          (preserved : original.current.native.config.store.BindingRefines
            repaired.current.native.config.store) :
          leftRaw.current.native.config.store.BindingRefines
            rightRaw.current.native.config.store := by
        have nativeEq : original.current.native = memory.native owner repaired.current.native := by
          rw [frame.current]
          rfl
        rw [nativeEq] at preserved
        exact supported.environment_refinement owner preserved runtime command moved
      refine ⟨nextMemory, rightRaw.normalize, ?_, nextOwned, candidates, paired, nextSupport,
        fun entryRef currentRef => refineStores entryRef (rawRefinement currentRef)⟩
      simp only [PhaseRuntimeState.environment, rightAllowed, ↓reduceIte]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨native, moved, rfl⟩

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The actual application command retains the entire external execution
prefix. The original public sample is also the repaired sample; its scheduler
and pending-observation likelihoods are consequently unchanged. -/
theorem environment_external_repair (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (supported : memory.CompletedAt right.application.current.native.config)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (command : EnvironmentCommand graph) (next : (app).Execution)
    (reached : next ∈ (left.environmentStep app (.application command)).support) :
    ∃ (nextMemory : BindingShadow graph) (image : (app).Execution),
      image ∈ (right.environmentStep app (.application command)).support ∧
      nextMemory.OwnBindings owner ∧ nextMemory.candidates = memory.candidates ∧
      PhaseStateFrame nextMemory owner next.application image.application ∧
      nextMemory.CompletedAt image.application.current.native.config ∧
      next.network = image.network ∧
      phaseExternalObservation runtime leaks owner next =
        phaseExternalObservation runtime leaks owner image ∧
      (left.application.entry.native.config.store.BindingRefines
          right.application.entry.native.config.store →
        left.application.current.native.config.store.BindingRefines
          right.application.current.native.config.store →
        next.application.entry.native.config.store.BindingRefines
          image.application.entry.native.config.store ∧
        next.application.current.native.config.store.BindingRefines
          image.application.current.native.config.store) := by
  classical
  let finish (physical : (app).Execution) (state : PhaseRuntimeState graph) : (app).Execution :=
    { physical with
      application := state
      environmentRecall := physical.environmentRecall ++
        [⟨physical.observeEnvironment app, .application command⟩] }
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, frame.publicView owned]
    rfl
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
  change next ∈ ((left.application.environment runtime command).map (finish left)).support
    at reached
  obtain ⟨state, moved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  obtain ⟨nextMemory, image, imageMoved, nextOwned, candidates, paired, nextSupport,
      refineStores⟩ :=
    frame.environment_repair owned supported runtime command state moved
  have actual : finish right image ∈
      (right.environmentStep app (.application command)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change finish right image ∈
      ((right.application.environment runtime command).map (finish right)).support
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨image, imageMoved, rfl⟩
  have nextService : (finish left state).environmentRecall =
      (finish right image).environmentRecall := by
    change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
    rw [service, before]
  refine ⟨nextMemory, finish right image, actual, nextOwned, candidates, paired, nextSupport,
    network, ?_, refineStores⟩
  exact phaseExternalObservation_congr runtime leaks _ _ owner network receipts nextService
    (paired.publicView nextOwned) (paired.playerView_other nextOwned) recalled

end Vegas.EventGraphRuntime.BindingShadow
