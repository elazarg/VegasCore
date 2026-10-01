/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveRecallInvariant

/-! # Recorded public views stay current until an event completes

Every scheduler command either leaves the graph configuration, the accepted
handles and the activation times unchanged, or appends one completion to the
history. Player responses change none of them. So a recorded response's public
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

omit [DecidableEq Player] in
/-- Either the configuration, accepted handles and activation times are
unchanged, or one completion is appended to the history. -/
def PublicStep (before after : State graph) : Prop :=
  (after.config = before.config ∧ after.accepted = before.accepted ∧
      after.activatedAt = before.activatedAt) ∨
    ∃ completion, after.config.history = before.config.history ++ [completion]

omit [DecidableEq Player] in
theorem PublicStep.refl (state : State graph) : PublicStep state state :=
  Or.inl ⟨rfl, rfl, rfl⟩

theorem publicStep_handle (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) : PublicStep state next := by
  obtain ⟨event, _, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  exact Or.inr ⟨⟨event, action⟩, state.config.step_history event ready action next.config member⟩

omit [DecidableEq Player] in
theorem publicStep_environmentStep (state next : State graph) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support) :
    PublicStep state next := by
  have accepted := (environmentStep_tables runtime state next command member).1
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at member
      subst next
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | executeSample event =>
      rcases (environmentStep_executeSample_config_activated runtime state next event member).2
        with ⟨configEq, activatedEq⟩ | ⟨ready, action, stepped, _⟩
      · exact Or.inl ⟨configEq, accepted, activatedEq⟩
      · exact Or.inr ⟨⟨event, action⟩, state.config.step_history event ready action _ stepped⟩
  | expire event =>
      rcases (environmentStep_expire_config_activated runtime state next event member).2
        with ⟨configEq, activatedEq⟩ | ⟨ready, action, stepped, _⟩
      · exact Or.inl ⟨configEq, accepted, activatedEq⟩
      · exact Or.inr ⟨⟨event, action⟩, state.config.step_history event ready action _ stepped⟩

/-- Every scheduler command takes one public step of the application. -/
theorem publicStep_reactive_environmentStep
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    PublicStep execution.application next.application := by
  unfold ReactiveApplication.Execution.environmentStep at reached
  rw [PMF.support_map] at reached
  obtain ⟨updated, supported, rfl⟩ := reached
  cases command with
  | activate who =>
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact PublicStep.refl _
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact PublicStep.refl _
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change PublicStep execution.application
        (execution.includePending (runtime.reactiveApplication leaks) id).application
      unfold ReactiveApplication.Execution.includePending
      cases execution.network.includePending id with
      | mk envelope network =>
          cases envelope with
          | none => exact PublicStep.refl _
          | some envelope =>
              change PublicStep execution.application
                ((handle runtime execution.application
                  ⟨envelope.id, envelope.payload.call⟩).getD execution.application)
              cases accepted : handle runtime execution.application
                  ⟨envelope.id, envelope.payload.call⟩ with
              | none => exact PublicStep.refl _
              | some next => exact publicStep_handle runtime _ next _ accepted
  | application command =>
      rw [PMF.support_map] at supported
      obtain ⟨state, changed, rfl⟩ := supported
      exact publicStep_environmentStep runtime _ state command changed

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
    obtain ⟨prefixBefore, equalBefore⟩ := valid observer entry member
    rcases publicStep_reactive_environmentStep runtime leaks execution next command reached with
      ⟨configEq, acceptedEq, activatedEq⟩ | ⟨completion, historyEq⟩
    · have observationEq : next.application.publicView.observation =
          execution.application.publicView.observation := by
        change graph.publicObserve next.application.config =
          graph.publicObserve execution.application.config
        rw [configEq]
      have orderEq : next.application.publicView.observation.completionOrder =
          execution.application.publicView.observation.completionOrder := by
        rw [observationEq]
      refine ⟨orderEq ▸ prefixBefore, fun equal => ?_⟩
      obtain ⟨sameObservation, sameAccepted, sameActivated⟩ := equalBefore (equal.trans orderEq)
      refine ⟨sameObservation.trans observationEq.symm, ?_, ?_⟩
      · change _ = next.application.accepted
        rw [acceptedEq]
        exact sameAccepted
      · change _ = next.application.activatedAt
        rw [activatedEq]
        exact sameActivated
    · have orderEq : next.application.publicView.observation.completionOrder =
          execution.application.publicView.observation.completionOrder ++ [completion.event] := by
        change next.application.config.history.map EventGraph.Completion.event =
          execution.application.config.history.map EventGraph.Completion.event ++ [completion.event]
        rw [historyEq, List.map_append, List.map_singleton]
      refine ⟨orderEq ▸ prefixBefore.trans (List.prefix_append _ _), fun equal => ?_⟩
      exfalso
      have lengths := congrArg List.length equal
      rw [orderEq, List.length_append, List.length_singleton] at lengths
      have bounded := prefixBefore.length_le
      omega

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
