/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveRecallInvariant
import Vegas.Pending.PublicFailureEvidence

/-! # Recorded public views stay current until an event completes

Every scheduler command has a finite completion footprint. Elementary
footprints preserve the graph, accepted handles and activation times, or
append one completion to the history. Player responses change none of them.
A recorded response's public
view has a completion order that is a prefix of the current one, and while no
event has completed since, its public observation, accepted handles and
activation times are the current ones. This holds at every legal history, for
every scheduler and arbitrary responses.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A recorded response's public view: its completion order is a prefix of the
current one, and while no event has completed since, its public observation,
accepted handles and activation times are the current ones. -/
def EntryStable (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who,
    entry.beforeView.application.publicView.observation.completionOrder <+:
        execution.application.publicView.observation.completionOrder ∧
      (entry.beforeView.application.publicView.observation.completionOrder =
          execution.application.publicView.observation.completionOrder →
        entry.beforeView.application.publicView.observation =
            execution.application.publicView.observation ∧
          entry.beforeView.application.publicView.accepted =
            execution.application.publicView.accepted ∧
          entry.beforeView.application.publicView.activatedAt =
            execution.application.publicView.activatedAt)

private theorem retained_public_view_step (saved : PublicView graph)
    (before after : State graph) (step : CompletionStep before after)
    (valid : saved.observation.completionOrder <+: before.publicView.observation.completionOrder ∧
      (saved.observation.completionOrder = before.publicView.observation.completionOrder →
        saved.observation = before.publicView.observation ∧
          saved.accepted = before.accepted ∧ saved.activatedAt = before.activatedAt)) :
    saved.observation.completionOrder <+: after.publicView.observation.completionOrder ∧
      (saved.observation.completionOrder = after.publicView.observation.completionOrder →
        saved.observation = after.publicView.observation ∧
          saved.accepted = after.accepted ∧ saved.activatedAt = after.activatedAt) := by
  obtain ⟨prefixBefore, equalBefore⟩ := valid
  rcases step with ⟨configEq, acceptedEq, activatedEq⟩ |
      ⟨event, ready, action, supported, _activated, _accepted⟩
  · have observationEq : after.publicView.observation = before.publicView.observation := by
      change graph.publicObserve after.config = graph.publicObserve before.config
      rw [configEq]
    have orderEq : after.publicView.observation.completionOrder =
        before.publicView.observation.completionOrder := by rw [observationEq]
    refine ⟨orderEq ▸ prefixBefore, fun equal => ?_⟩
    obtain ⟨sameObservation, sameAccepted, sameActivated⟩ := equalBefore (equal.trans orderEq)
    exact ⟨sameObservation.trans observationEq.symm,
      sameAccepted.trans acceptedEq.symm, sameActivated.trans activatedEq.symm⟩
  · have orderEq : after.publicView.observation.completionOrder =
        before.publicView.observation.completionOrder ++ [event] := by
      exact before.config.step_history_events event ready action after.config supported
    refine ⟨orderEq ▸ prefixBefore.trans (List.prefix_append _ _), fun equal => ?_⟩
    exfalso
    have lengths := congrArg List.length equal
    rw [orderEq, List.length_append, List.length_singleton] at lengths
    have bounded := prefixBefore.length_le
    omega

/-- Recorded public views stay current until an event completes, for every
scheduler and arbitrary responses. -/
theorem entryStable_serviceInvariant (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (EntryStable runtime leaks) where
  respond execution who action valid := by
    let app := runtime.reactiveApplication leaks
    have publicEq := (runtime.reactive_respond_application leaks execution who action).2
    intro observer entry member
    change entry.beforeView.application.publicView.observation.completionOrder <+:
        (execution.respond app who action).application.publicView.observation.completionOrder ∧ _
    rw [publicEq]
    rcases app.respond_entry_origin execution who observer action entry member with
      prior | ⟨_, fresh⟩
    · exact valid observer entry prior
    · rw [fresh]
      exact ⟨List.prefix_refl _, fun _ => ⟨rfl, rfl, rfl⟩⟩
  environment execution next command valid _ reached := by
    let app := runtime.reactiveApplication leaks
    have recallEq := app.environmentStep_recall execution next command reached
    intro observer entry member
    rw [recallEq] at member
    let saved := entry.beforeView.application.publicView
    let retained (current : State graph) : Prop :=
      saved.observation.completionOrder <+: current.publicView.observation.completionOrder ∧
        (saved.observation.completionOrder = current.publicView.observation.completionOrder →
          saved.observation = current.publicView.observation ∧
            saved.accepted = current.accepted ∧ saved.activatedAt = current.activatedAt)
    have preserved : ∀ {before after : State graph},
        Relation.ReflTransGen CompletionStep before after → retained before → retained after := by
      intro before after path
      induction path using Relation.ReflTransGen.head_induction_on with
      | refl => exact id
      | @head before middle moved _ ih =>
          exact fun prior => ih (retained_public_view_step saved before middle moved prior)
    exact preserved (completionPath_reactive_environmentStep runtime leaks execution next command
      reached) (valid observer entry member)

/-- Recorded public views stay current until an event completes, at every
legal history. -/
theorem entryStable_history (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      state) :
    ReactiveApplication.serviceInvariant (EntryStable runtime leaks) state :=
  (entryStable_serviceInvariant runtime leaks scheduler).history initial horizon
    (fun state _ who entry member => by
      simp [ReactiveApplication.Execution.initial] at member) trace

end Vegas.EventGraphRuntime
