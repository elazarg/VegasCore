/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseArchivedSourceObservation

/-! # Original saved owner words at retired source attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhasePublicView

/-- Read the old saved own prefix before inserting all earlier retired choices.
The old native store and completion order remain available for source decoding. -/
def archivedSavedObservation? (view : PhasePublicView graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (current : graph.PlayerObservation who) (index : Nat) :
    Option (CommitAttemptId × graph.PlayerObservation who) :=
  (view.retired[index]?).map fun record =>
    let old := record.2.recoverPlayerObservation who candidates current record.1.phase
    let prior := { view with retired := view.retired.take index }
    let saved := old.ownActions.filter fun completion => completion.event.val < record.1.phase
    (record.1, { old with ownActions := prior.archivedOwnHistory who candidates saved })

end PhasePublicView

/-- The saved prefix at a retired attempt is recovered from the actual current
observation. Filtering precedes archive insertion, so earlier voided choices at
the same static addresses remain in the source word. -/
theorem phaseArchivedSavedObservation_observed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (index : Nat) (record : RetiredCommitAttempt graph)
    (selected : control.execution.application.retired[index]? = some record) (who : Player) :
    control.execution.application.publicView.archivedSavedObservation? who
        (control.execution.application.current.native.playerView who).candidates
        (graph.playerObserve who control.execution.application.current.native.config) index =
      some (record.attempt,
        ({ graph.playerObserve who record.state.config with
          ownActions := graph.ownCompletions who
            (PhaseRuntimeState.archivedHistory (control.execution.application.retired.take index)
              (record.state.config.history.filter fun completion =>
                completion.event.val < record.attempt.phase)) }
            : graph.PlayerObservation who)) := by
  have member := List.mem_of_getElem? selected
  have physical := phaseArchivedPlayerObservation_observed runtime leaks plan inputs horizon
    scheduler trace record member who
  have intervals := phaseRetiredBindingInterval_history runtime leaks plan inputs horizon
    scheduler trace
  have read : ∀ previous ∈ control.execution.application.retired.take index,
      previous.state.publicView.bindingHistory who
          (control.execution.application.current.native.playerView who).candidates
          previous.attempt.phase =
        graph.ownCompletions who (previous.state.config.history.filter fun completion =>
          previous.attempt.phase ≤ completion.event.val) := by
    intro previous within
    have retained := List.mem_of_mem_take within
    obtain ⟨valid, ⟨original, native⟩, fixed⟩ :=
      phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler trace
        previous retained
    exact valid.bindingHistory_eq native.reachable fixed who previous.attempt.phase
      (fun completion recorded lower acting =>
        intervals.binding_fields previous retained completion recorded lower who acting)
  have word := PhaseRuntimeState.archivedHistory_readout
    (control.execution.application.retired.take index)
    (record.state.config.history.filter fun completion =>
      completion.event.val < record.attempt.phase) who
    (control.execution.application.current.native.playerView who).candidates read
  simp only [PhasePublicView.archivedSavedObservation?, PhaseRuntimeState.publicView,
    List.getElem?_map, selected, Option.map_some]
  rw [physical]
  apply congrArg (fun observation => some (record.attempt, observation))
  apply EventGraph.PlayerObservation.ext
  · rfl
  · rfl
  · simpa only [PhasePublicView.archivedOwnHistory, PhaseRuntimeState.publicView,
      List.map_take, EventGraph.playerObserve_ownActions, EventGraph.ownCompletions,
      List.filter_filter, Bool.and_comm] using word

/-- The full actual owner input fixes every retired saved-prefix observation,
including all earlier voided choices at the same static event addresses. -/
theorem phaseArchivedSavedObservations_eq_of_observed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second))
    (who : Player) (index : Nat)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who) :
    (first.execution.application.retired[index]?).map (fun record =>
        (record.attempt, ({ graph.playerObserve who record.state.config with
          ownActions := graph.ownCompletions who (PhaseRuntimeState.archivedHistory
            (first.execution.application.retired.take index)
              (record.state.config.history.filter fun completion =>
                completion.event.val < record.attempt.phase)) }
            : graph.PlayerObservation who))) =
      (second.execution.application.retired[index]?).map (fun record =>
        (record.attempt, ({ graph.playerObserve who record.state.config with
          ownActions := graph.ownCompletions who (PhaseRuntimeState.archivedHistory
            (second.execution.application.retired.take index)
              (record.state.config.history.filter fun completion =>
                completion.event.val < record.attempt.phase)) }
            : graph.PlayerObservation who))) := by
  let recover : (phaseApplication runtime leaks).PlayerView →
      Option (CommitAttemptId × graph.PlayerObservation who) := fun view =>
    view.application.2.archivedSavedObservation? who view.application.1.candidates
      ⟨view.application.1.observation.completionOrder, view.application.1.observation.store,
        view.application.1.observation.ownActions⟩ index
  have read {control}
      (trace : ((phaseApplication runtime leaks).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
      recover (control.execution.observe (phaseApplication runtime leaks) who) =
        (control.execution.application.retired[index]?).map (fun record =>
          (record.attempt, ({ graph.playerObserve who record.state.config with
            ownActions := graph.ownCompletions who (PhaseRuntimeState.archivedHistory
              (control.execution.application.retired.take index)
                (record.state.config.history.filter fun completion =>
                completion.event.val < record.attempt.phase)) }
            : graph.PlayerObservation who))) := by
    cases selected : control.execution.application.retired[index]? with
    | none =>
        simp only [recover, PhasePublicView.archivedSavedObservation?,
          ReactiveApplication.Execution.observe, phaseApplication, PhaseRuntimeState.playerView,
          PhaseRuntimeState.publicView, List.getElem?_map, selected, Option.map_none]
    | some record =>
        rw [Option.map_some]
        exact phaseArchivedSavedObservation_observed runtime leaks plan inputs horizon scheduler
          trace index record selected who
  exact (read firstTrace).symm.trans ((congrArg recover observed).trans (read secondTrace))

end Vegas.EventGraphRuntime
