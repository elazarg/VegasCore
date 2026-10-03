/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingReceipts
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveReceipts

/-! # Accepted binding associations have actual accepting receipts

Every event handle accepted on an initialized raw history originated in a
real ledger commitment whose receipt reports acceptance. Submission, passive
observation and application commands cannot create a fictitious association.
The property holds for usable and unusable private material alike.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def AcceptedBindingReceipts (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ event candidate, execution.application.accepted (.inr event) = some candidate →
    ∃ message ∈ execution.network.ledger,
      message.sender = candidate.1 ∧ message.payload.call = .commitment event candidate ∧
        (message.id, true) ∈ execution.receipts

private theorem AcceptedBindingReceipts.copy
    {before after : (runtime.reactiveApplication leaks).Execution}
    (valid : runtime.AcceptedBindingReceipts leaks before)
    (accepted : after.application.accepted = before.application.accepted)
    (ledger : before.network.ledger ⊆ after.network.ledger)
    (receipts : before.receipts ⊆ after.receipts) :
    runtime.AcceptedBindingReceipts leaks after := by
  intro event candidate stored
  obtain ⟨message, published, authored, call, receipt⟩ :=
    valid event candidate (accepted ▸ stored)
  exact ⟨message, ledger published, authored, call, receipts receipt⟩

private theorem acceptedBindingReceipts_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (valid : runtime.AcceptedBindingReceipts leaks execution) :
    runtime.AcceptedBindingReceipts leaks
      (execution.respond (runtime.reactiveApplication leaks) who response) := by
  apply valid.copy runtime leaks
  · exact congrArg PublicView.accepted
      (runtime.reactive_respond_application leaks execution who response).2
  · rcases response with ⟨transmission⟩
    cases transmission <;> exact List.Subset.refl _
  · rw [ReactiveApplication.respond_receipts]

private theorem acceptedBindingReceipts_includePending
    (execution : (runtime.reactiveApplication leaks).Execution) (id : MessageId Player)
    (valid : runtime.AcceptedBindingReceipts leaks execution) :
    runtime.AcceptedBindingReceipts leaks
      (execution.includePending (runtime.reactiveApplication leaks) id) := by
  let app := runtime.reactiveApplication leaks
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact valid
  | some message =>
      have identified : message.id = id := by
        have selected := (List.find?_eq_some_iff_append.mp found).1
        simpa only [decide_eq_true_eq] using selected
      change runtime.AcceptedBindingReceipts leaks { execution with
        application := (app.handle execution.application message).getD execution.application
        network := { execution.network with
          pending := MessagePool.removeFirst id execution.network.pending
          ledger := execution.network.ledger ++ [message] }
        receipts := execution.receipts ++
          [(id, (app.handle execution.application message).isSome)] }
      cases accepted : app.handle execution.application message with
      | none =>
          simp only [Option.getD_none]
          apply valid.copy runtime leaks
          · rfl
          · exact fun _ member => List.mem_append_left _ member
          · exact fun _ member => List.mem_append_left _ member
      | some next =>
          simp only [Option.getD_some]
          intro event candidate stored
          have handled := reactiveHandle_call accepted
          change next.accepted (.inr event) = some candidate at stored
          cases call : message.payload.call with
          | commitment addressed chosen =>
              have raw : handle runtime execution.application
                  ⟨message.id, .commitment addressed chosen⟩ = some next := by
                simpa only [call] using handled
              have tables := handle_commitment_tables runtime execution.application next
                message.id addressed chosen raw
              rw [tables.2.1] at stored
              by_cases same : event = addressed
              · subst event
                rw [Function.update_self] at stored
                cases Option.some.inj stored
                refine ⟨message, List.mem_append_right _ (List.mem_singleton_self _),
                  tables.2.2.symm, call, ?_⟩
                change (message.id, true) ∈ execution.receipts ++ [(id, true)]
                rw [identified]
                exact List.mem_append_right _ (List.mem_singleton_self _)
              · rw [Function.update_of_ne (fun equal => same (Sum.inr.inj equal))] at stored
                obtain ⟨prior, published, authored, priorCall, receipt⟩ :=
                  valid event candidate stored
                exact ⟨prior, List.mem_append_left _ published, authored, priorCall,
                  List.mem_append_left _ receipt⟩
          | opening addressed handle raw | withhold addressed =>
              have tables := handle_resolution_tables runtime execution.application next
                ⟨message.id, message.payload.call⟩ (by intros; simp [call]) handled
              rw [tables.1] at stored
              obtain ⟨prior, published, authored, priorCall, receipt⟩ :=
                valid event candidate stored
              exact ⟨prior, List.mem_append_left _ published, authored, priorCall,
                List.mem_append_left _ receipt⟩
          | malformed raw => simp only [call, handle] at handled; cases handled

private theorem acceptedBindingReceipts_environment
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (valid : runtime.AcceptedBindingReceipts leaks execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.AcceptedBindingReceipts leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact acceptedBindingReceipts_includePending runtime leaks execution id valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid.copy runtime leaks (environmentStep_tables runtime execution.application state
        command changed).1 (List.Subset.refl _) (List.Subset.refl _)

/-- On every legal initialized raw history, each accepted binding association
has an actual ledger commitment and the accepting receipt for its identifier. -/
theorem acceptedBindingReceipts_history (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) :
    runtime.AcceptedBindingReceipts leaks control.execution := by
  have invariant : (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (runtime.AcceptedBindingReceipts leaks) := {
    respond := fun execution who response valid =>
      acceptedBindingReceipts_respond runtime leaks execution who response valid
    environment := fun execution next command valid _ reached =>
      acceptedBindingReceipts_environment runtime leaks execution next command valid reached }
  exact invariant.history (inputs.map State.initial) horizon (by
    intro state supported event candidate accepted
    obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
    obtain ⟨input, owner, payload, impossible, _⟩ :=
      State.initial_accepted_eq_some initial (.inr event) candidate accepted
    cases impossible) trace

end Vegas.EventGraphRuntime
