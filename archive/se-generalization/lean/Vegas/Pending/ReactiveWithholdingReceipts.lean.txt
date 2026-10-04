/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveReceipts
import Interaction.ReactiveMessageIdentity

/-! # Accepting withholding receipts certify immutable public failure

A TRUE receipt for withholding identifies a real ledger envelope whose
publication output is failure. Later raw submissions and scheduler commands
cannot replace that output. This uses the actual handler, including its
remembered intentions, without prescribing the author's later policy.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- An accepted withholding packet stores public failure, even if the handler
retains an earlier private disclosure intention with the same result. -/
theorem handle_withhold_output_failure
    (state next : State graph) (id : MessageId Player) (event : graph.EventId)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .publication payload)
    (accepted : handle runtime state ⟨id, .withhold event⟩ = some next) :
    next.config.outputs event = some
      (cast (congrArg EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases node : nodeView graph event with
      | bind owner actual actualEq codeEq | sample actual law actualEq codeEq =>
          simp [handle, ready, timely, node] at accepted
      | resolve owner actual binding checks actualEq codeEq =>
          have same : actual = payload :=
            EventField.publication.inj (actualEq.symm.trans outputEq)
          subst actual
          by_cases sender : id.1 = owner
          · obtain ⟨disclose, _resolved, handled⟩ := runtime.handle_withhold_failure_eq state id
              event owner payload binding checks actualEq codeEq node ready timely sender
            rw [handled] at accepted
            cases Option.some.inj accepted
            exact state.config.complete_output_same event ready _ _
          · simp [handle, ready, timely, node, Message.sender, sender] at accepted
    · simp [handle, ready, timely] at accepted
  · simp [handle, ready] at accepted

/-- Every accepting receipt has its actual ledger envelope. If that envelope
is withholding, its corresponding publication field still contains failure. -/
def WithholdingReceipts (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ id, (id, true) ∈ execution.receipts →
    ∃ message ∈ execution.network.ledger, message.id = id ∧
      ∀ event payload (outputEq : graph.outputLayout event = .publication payload),
        message.payload.call = .withhold event →
          execution.application.config.outputs event = some
            (cast (congrArg EventField.Value outputEq.symm)
              (PublicationResult.failure : PublicationResult (L.Val payload)))

private theorem withholdingReceipts_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (valid : runtime.WithholdingReceipts leaks execution) :
    runtime.WithholdingReceipts leaks
      (execution.respond (runtime.reactiveApplication leaks) who response) := by
  have same := (runtime.reactive_respond_application leaks execution who response).1
  rcases response with ⟨transmission⟩
  cases transmission <;> intro id receipt <;>
    obtain ⟨message, published, identified, recorded⟩ := valid id receipt <;>
    refine ⟨message, published, identified, ?_⟩ <;>
    intro event payload outputEq call <;>
    exact (congrArg (fun config : graph.Config => config.outputs event) same).trans
      (recorded event payload outputEq call)

private theorem withholdingReceipts_includePending
    (execution : (runtime.reactiveApplication leaks).Execution) (id : MessageId Player)
    (valid : runtime.WithholdingReceipts leaks execution) :
    runtime.WithholdingReceipts leaks
      (execution.includePending (runtime.reactiveApplication leaks) id) := by
  let app := runtime.reactiveApplication leaks
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact valid
  | some message =>
      have identified : message.id = id := by
        have selected := (List.find?_eq_some_iff_append.mp found).1
        simpa only [decide_eq_true_eq] using selected
      intro received receipt
      change (received, true) ∈ execution.receipts ++
        [(id, (app.handle execution.application message).isSome)] at receipt
      rcases List.mem_append.mp receipt with prior | fresh
      · obtain ⟨earlier, published, earlierId, recorded⟩ := valid received prior
        refine ⟨earlier, List.mem_append_left _ published, earlierId, ?_⟩
        intro event payload outputEq call
        have stored := recorded event payload outputEq call
        have kept := (ReactiveApplication.Invariant.includePending
          (runtime.reactiveStoreInvariant leaks (.inr event) _)
            execution id stored)
        simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found, Config.store_output] using kept
      · obtain ⟨same, successful⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
        obtain ⟨next, handled⟩ := Option.isSome_iff_exists.mp successful.symm
        refine ⟨message, List.mem_append_right _ (List.mem_singleton.mpr rfl),
          identified.trans same.symm, ?_⟩
        intro event payload outputEq call
        have raw : handle runtime execution.application
            ⟨message.id, .withhold event⟩ = some next := by
          simpa only [call] using reactiveHandle_call handled
        change
          ((app.handle execution.application message).getD execution.application).config.outputs
            event = _
        rw [handled, Option.getD_some]
        exact runtime.handle_withhold_output_failure execution.application next message.id event
          payload outputEq raw

private theorem withholdingReceipts_environment
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (valid : runtime.WithholdingReceipts leaks execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.WithholdingReceipts leaks next := by
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
      exact withholdingReceipts_includePending runtime leaks execution id valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      intro id receipt
      obtain ⟨message, published, identified, recorded⟩ := valid id receipt
      refine ⟨message, published, identified, ?_⟩
      intro event payload outputEq call
      exact environmentStep_store_of_some runtime execution.application state command changed
        (.inr event) _ (recorded event payload outputEq call)

/-- Every initialized raw history, for arbitrary responses and public
scheduling, keeps the exact failure certified by its withholding receipts. -/
theorem withholdingReceipts_history (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) :
    runtime.WithholdingReceipts leaks control.execution := by
  have invariant : (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (runtime.WithholdingReceipts leaks) := {
    respond := fun execution who response valid =>
      withholdingReceipts_respond runtime leaks execution who response valid
    environment := fun execution next command valid _ reached =>
      withholdingReceipts_environment runtime leaks execution next command valid reached }
  exact invariant.history (inputs.map State.initial) horizon (by
    intro state supported id receipt
    simp only [ReactiveApplication.Execution.initial, List.not_mem_nil] at receipt) trace

/-- The accepting receipt of THIS emitted withholding packet fixes its public
result. Unique authenticated identifiers exclude a different ledger envelope. -/
theorem withhold_receipt_output_failure (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (message : Message Player (WitnessedPacket graph))
    (emitted : message ∈ control.execution.network.inputs)
    (accepted : (message.id, true) ∈ control.execution.receipts)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .publication payload)
    (call : message.payload.call = .withhold event) :
    control.execution.application.config.outputs event = some
      (cast (congrArg EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  obtain ⟨actual, published, identified, output⟩ :=
    runtime.withholdingReceipts_history leaks inputs horizon scheduler control trace
      message.id accepted
  have unique := (runtime.reactiveApplication leaks).uniqueIds_history scheduler
    (inputs.map State.initial) horizon control trace
  have same := (unique.ledger actual published).inputs message emitted identified.symm
  subst actual
  exact output event payload outputEq call

end Vegas.EventGraphRuntime
