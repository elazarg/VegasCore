/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingClearCommandLaw
import Vegas.Pending.PhaseBindingOpaqueStep
import Vegas.Game.PhaseTimingMemory

/-! # Original application-command likelihoods of complete operational observations -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A command's actual joint operational channel is independent of arbitrary
hidden binding values on its clear branch. The entire physical network,
scheduler recall, foreign private inputs and owner erased word are retained.
First public exclusion maps to absence; no reset-memory equality is asserted. -/
theorem phase_binding_clear_command_observation_law
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (past : (left.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (clear : right.application.current.excluded = ∅)
    (opaquePhase : ∀ phase ∈ right.application.phases.head?, phase.kind = .commitment)
    (command : EnvironmentCommand graph) :
    let observe := fun physical : (app).Execution =>
      (phaseExternalObservation runtime leaks owner physical,
        phaseOperationalView runtime leaks (physical.observe app owner),
        (physical.recall owner).map fun entry =>
          (phaseOperationalView runtime leaks entry.beforeView, entry.emitted))
    ((left.environmentStep app (.application command)).map fun next =>
      if next.application.current.excluded = ∅ then some (observe next) else none) =
      ((right.environmentStep app (.application command)).map fun next =>
        if next.application.current.excluded = ∅ then some (observe next) else none) := by
  classical
  intro observe
  let finish (physical : (app).Execution) (state : PhaseRuntimeState graph) : (app).Execution :=
    { physical with
      application := state
      environmentRecall := physical.environmentRecall ++
        [⟨physical.observeEnvironment app, .application command⟩] }
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application, BindingShadow.phased_publicView owned]
    rfl
  have logs : left.environmentRecall ++ [⟨left.observeEnvironment app,
      (ReactiveApplication.Command.application command)⟩] =
      right.environmentRecall ++ [⟨right.observeEnvironment app, .application command⟩] := by
    rw [service, before]
  have sameObserved (state : PhaseRuntimeState graph) :
      observe (finish left (memory.phased owner state)) = observe (finish right state) := by
    have current : (finish left (memory.phased owner state)).application =
        memory.phased owner (finish right state).application := rfl
    have op := phaseOperationalView_memory runtime leaks memory owner owned valid
      (finish left (memory.phased owner state)) (finish right state) current network receipts
    dsimp only [observe]
    apply Prod.ext
    · unfold phaseExternalObservation
      refine Prod.ext network (Prod.ext receipts (Prod.ext logs (Prod.ext ?_ ?_)))
      · change (⟨left.network.publicView, (memory.phased owner state).publicView,
          left.receipts⟩ : (app).EnvironmentView) = ⟨_, state.publicView, _⟩
        rw [network, receipts, BindingShadow.phased_publicView owned]
      · funext who
        by_cases same : who = owner
        · simp only [same, ite_true]
        · simp only [same, ite_false]
          apply congrArg some
          apply Prod.ext (recalled who same)
          change (⟨left.network.observe who, (memory.phased owner state).playerView who,
            left.receipts⟩ : (app).PlayerView) = ⟨_, state.playerView who, _⟩
          rw [network, receipts, BindingShadow.phased_playerView_other owned state who same]
    · exact Prod.ext op past
  have commandLaw := BindingShadow.environment_clear_observation_law runtime memory owner owned
    right.application clear opaquePhase command
  have lifted := congrArg (fun law : PMF (Option (PhaseRuntimeState graph)) =>
    law.map (fun next => next.map (fun state => observe (finish left state)))) commandLaw
  simp only [PMF.map_comp, Function.comp_def, apply_ite, Option.map_some, Option.map_none,
    sameObserved] at lifted
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  change ((left.application.environment runtime command).map fun state =>
    if state.current.excluded = ∅ then some (observe (finish left state)) else none) =
      ((right.application.environment runtime command).map fun state =>
        if state.current.excluded = ∅ then some (observe (finish right state)) else none)
  rw [application]
  exact lifted

end Vegas
