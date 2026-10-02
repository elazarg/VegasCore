/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveAssociationPersistence
import Interaction.ReactiveServiceInvariant

/-! # Accepted binding receipts retain their selected handles

An accepting receipt identifies its ledger envelope. If that envelope is a
commitment, its selected handle remains in the public application state after
arbitrary later player responses and scheduler commands. This concerns actual
receipts and accepted associations, including opaque or unusable bindings.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def BindingReceipts (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ id, (id, true) ∈ execution.receipts →
    ∃ message ∈ execution.network.ledger, message.id = id ∧
      ∀ event candidate, message.payload.call = .commitment event candidate →
        execution.application.accepted (.inr event) = some candidate

theorem bindingReceipts_respond (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (valid : runtime.BindingReceipts leaks execution) :
    runtime.BindingReceipts leaks
      (execution.respond (runtime.reactiveApplication leaks) who response) := by
  have accepted := congrArg PublicView.accepted
    (runtime.reactive_respond_application leaks execution who response).2
  rcases response with ⟨transmission⟩
  cases transmission <;> intro id receipt <;>
    obtain ⟨message, published, identified, recorded⟩ := valid id receipt <;>
    refine ⟨message, published, identified, ?_⟩ <;>
    intro event candidate call <;>
    exact (congrFun accepted (.inr event)).trans (recorded event candidate call)

private theorem bindingReceipts_includePending
    (execution : (runtime.reactiveApplication leaks).Execution) (id : MessageId Player)
    (binding : execution.application.BindingInvariant)
    (valid : runtime.BindingReceipts leaks execution) :
    runtime.BindingReceipts leaks
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
        intro event candidate call
        have kept := (ReactiveApplication.Invariant.includePending
          (runtime.reactiveAssociationInvariant leaks (.inr event) candidate)
            execution id ⟨binding, recorded event candidate call⟩).2
        simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found] using kept
      · obtain ⟨same, successful⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
        obtain ⟨next, handled⟩ := Option.isSome_iff_exists.mp successful.symm
        refine ⟨message, List.mem_append_right _ (List.mem_singleton.mpr rfl),
          identified.trans same.symm, ?_⟩
        intro event candidate call
        have raw : handle runtime execution.application
            ⟨message.id, .commitment event candidate⟩ = some next := by
          simpa only [call] using reactiveHandle_call handled
        have tables := handle_commitment_tables runtime execution.application next message.id
          event candidate raw
        change ((app.handle execution.application message).getD execution.application).accepted
          (.inr event) = some candidate
        rw [handled, Option.getD_some, tables.2.1, Function.update_self]

theorem bindingReceipts_environment
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (binding : execution.application.BindingInvariant)
    (valid : runtime.BindingReceipts leaks execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.BindingReceipts leaks next := by
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
      exact bindingReceipts_includePending runtime leaks execution id binding valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      intro id receipt
      obtain ⟨message, published, identified, recorded⟩ := valid id receipt
      refine ⟨message, published, identified, ?_⟩
      intro event candidate call
      exact (congrFun (environmentStep_tables runtime execution.application state command
        changed).1 (.inr event)).trans (recorded event candidate call)

theorem bindingReceipts_serviceInvariant
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler (fun execution =>
      execution.application.BindingInvariant ∧ runtime.BindingReceipts leaks execution) where
  respond execution who response valid :=
    ⟨(runtime.reactiveBindingInvariant leaks).respond execution who response valid.1,
      runtime.bindingReceipts_respond leaks execution who response valid.2⟩
  environment execution next command valid _ reached :=
    ⟨(runtime.reactiveBindingInvariant leaks).environmentStep
        execution next command valid.1 reached,
      runtime.bindingReceipts_environment leaks execution next command valid.1 valid.2 reached⟩

/-- Sound at every legal history without restrictions on the scheduler or responses. -/
theorem bindingReceipts_history (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) :
    runtime.BindingReceipts leaks control.execution := by
  have valid := (runtime.bindingReceipts_serviceInvariant leaks scheduler).history
    (inputs.map State.initial) horizon (by
      intro state supported
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨State.initial_bindingInvariant input, ?_⟩
      intro id receipt
      simp only [ReactiveApplication.Execution.initial, List.not_mem_nil] at receipt) trace
  exact valid.2

end Vegas.EventGraphRuntime
