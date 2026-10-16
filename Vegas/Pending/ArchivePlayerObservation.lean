/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ArchivePlayerStore
import Vegas.Pending.PhaseArchivedOwnPrefix
import Vegas.Pending.PhaseArchivedObservation

/-! # Complete retired player observations from permanent physical recall -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PublicView

/-- Recover a retired own word in its public completion order. Older actions
remain in the current word; the retired binding suffix uses permanent candidates. -/
def recoverOwnActions (view : PublicView graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (current : List graph.Completion) (low : Nat) : List graph.Completion :=
  view.observation.completionOrder.filterMap fun event =>
    if graph.actor? event = some who then
      if event.val < low then current.find? (fun completion => completion.event = event)
      else view.bindingRecord? who candidates event
    else none

/-- A complete retired player observation reconstructed solely from archived
public data and the current original private observation. -/
def recoverPlayerObservation (view : PublicView graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (current : graph.PlayerObservation who) (low : Nat) : graph.PlayerObservation who where
  completionOrder := view.observation.completionOrder
  store := view.recoverPlayerStore who candidates current.store
  ownActions := view.recoverOwnActions who candidates current.ownActions low

end PublicView

omit [DecidableEq Player] in
private theorem find_completion (history : List graph.Completion)
    (unique : (history.map Completion.event).Nodup)
    (completion : graph.Completion) (member : completion ∈ history) :
    history.find? (fun other => other.event = completion.event) = some completion := by
  induction history with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with same | inside
      · subst head
        simp
      · have different : head.event ≠ completion.event := by
          intro same
          exact unique.1 (same ▸ List.mem_map.mpr ⟨completion, inside, rfl⟩)
        simpa only [List.find?_cons, decide_eq_false different, Bool.false_eq_true,
          ↓reduceIte] using ih unique.2 inside

namespace State

/-- The entire retired own action word is determined, including its saved prefix
and every accepted failed binding, by the original physical observation. -/
theorem BindingInvariant.recoverOwnActions_eq {state current : State graph}
    (valid : state.BindingInvariant) {inputs : graph.Inputs}
    (reachable : state.config.Reachable inputs) (fixed : KeepsFixedCandidates state current)
    (who : Player) (low : Nat)
    (earlierActions : (graph.ownCompletions who state.config.history).filter
        (fun completion => completion.event.val < low) =
      (graph.ownCompletions who current.config.history).filter
        (fun completion => completion.event.val < low))
    (bindings : ∀ completion ∈ state.config.history,
      low ≤ completion.event.val → graph.actor? completion.event = some who →
        ∃ payload, graph.outputLayout completion.event = .binding who payload) :
    state.publicView.recoverOwnActions who (current.playerView who).candidates
        (graph.playerObserve who current.config).ownActions low =
      graph.ownCompletions who state.config.history := by
  change (state.config.history.map Completion.event).filterMap _ = _
  rw [List.filterMap_map]
  have localRead : ∀ completion ∈ state.config.history,
      (if graph.actor? completion.event = some who then
        if completion.event.val < low then
          (graph.ownCompletions who current.config.history).find?
            (fun other => other.event = completion.event)
        else state.publicView.bindingRecord? who (current.playerView who).candidates
          completion.event
      else none) =
      (if graph.actor? completion.event = some who then some completion else none) := by
    intro completion member
    by_cases owned : graph.actor? completion.event = some who
    · simp only [owned, ↓reduceIte]
      by_cases earlier : completion.event.val < low
      · simp only [earlier, ↓reduceIte]
        have before : completion ∈ (graph.ownCompletions who state.config.history).filter
            (fun other => other.event.val < low) := by
          exact List.mem_filter.mpr
            ⟨List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using owned⟩,
            by simpa only [decide_eq_true_eq] using earlier⟩
        rw [earlierActions] at before
        exact find_completion _
          (current.config.history_nodup.sublist (List.filter_sublist.map _)) completion
          (List.mem_filter.mp before).1
      · simp only [earlier, ↓reduceIte]
        obtain ⟨payload, binding⟩ := bindings completion member (Nat.le_of_not_gt earlier) owned
        exact valid.bindingRecord?_of_recorded reachable fixed completion.event who payload
          binding completion.action member
    · simp only [owned, ↓reduceIte]
  simp only [Function.comp_def, EventGraph.playerObserve_ownActions]
  rw [List.filterMap_congr localRead]
  simp only [EventGraph.ownCompletions]
  induction state.config.history with
  | nil => rfl
  | cons completion remaining ih =>
      by_cases owned : graph.actor? completion.event = some who <;> simp [owned, ih]

end State

/-- Every retired full native player observation has this actual reconstruction
at arbitrary initialized raw histories, including histories with permanent exclusions. -/
theorem phaseArchivedPlayerObservation_observed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (record : RetiredCommitAttempt graph) (member : record ∈ control.execution.application.retired)
    (who : Player) :
    record.state.publicView.recoverPlayerObservation who
        (control.execution.application.current.native.playerView who).candidates
        (graph.playerObserve who control.execution.application.current.native.config)
        record.attempt.phase =
      graph.playerObserve who record.state.config := by
  apply EventGraph.PlayerObservation.ext
  · rfl
  · exact phaseArchivedPlayerStore_observed runtime leaks plan inputs horizon scheduler trace
      record member who
  · obtain ⟨binding, ⟨original, native⟩, fixed⟩ :=
      phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler trace record member
    have intervals :=
      phaseRetiredBindingInterval_history runtime leaks plan inputs horizon scheduler trace
    exact binding.recoverOwnActions_eq native.reachable fixed who record.attempt.phase
      (phaseRetiredOwnPrefix_history runtime leaks plan inputs horizon scheduler trace
        record member who)
      (fun completion recorded lower acting =>
        intervals.binding_fields record member completion recorded lower who acting)

/-- Equal actual observations determine complete retired native player
observations, not merely their public stores or surviving action prefixes. -/
theorem phaseArchivedPlayerObservations_eq_of_observed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second))
    (who : Player)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who) :
    first.execution.application.retired.map (fun record =>
        (record.attempt, graph.playerObserve who record.state.config)) =
      second.execution.application.retired.map (fun record =>
        (record.attempt, graph.playerObserve who record.state.config)) := by
  let recover : (phaseApplication runtime leaks).PlayerView →
      List (CommitAttemptId × graph.PlayerObservation who) := fun view =>
    view.application.2.retired.map fun record =>
      (record.1, record.2.recoverPlayerObservation who view.application.1.candidates
        ⟨view.application.1.observation.completionOrder,
          view.application.1.observation.store, view.application.1.observation.ownActions⟩
        record.1.phase)
  have read {control}
      (trace : ((phaseApplication runtime leaks).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
      recover (control.execution.observe (phaseApplication runtime leaks) who) =
        control.execution.application.retired.map (fun record =>
          (record.attempt, graph.playerObserve who record.state.config)) := by
    change (control.execution.application.retired.map
      (fun record => (record.attempt, record.state.publicView))).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro record member
    exact congrArg (fun observation => (record.attempt, observation))
      (phaseArchivedPlayerObservation_observed runtime leaks plan inputs horizon scheduler trace
        record member who)
  exact (read firstTrace).symm.trans ((congrArg recover observed).trans (read secondTrace))

end Vegas.EventGraphRuntime
