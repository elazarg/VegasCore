/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventOpponentFrame
import Interaction.ReactiveReceipts
import Interaction.ReactivePublication

/-! # At most one accepted envelope per source event

Every accepting receipt corresponds to a ledger envelope that completed its
addressed event. Completion is permanent, so another envelope for that event
cannot receive an accepting receipt. The invariant permits arbitrary initial
application states, raw responses, pending observations and schedulers.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def acceptedFor (execution : (runtime.reactiveApplication leaks).Execution)
    (event : graph.EventId) (id : MessageId Player) : Prop :=
  ∃ message, (message, (id, true)) ∈ execution.network.ledger.zip execution.receipts ∧
    message.payload.call.event? graph = some event

structure AcceptanceUnique (execution : (runtime.reactiveApplication leaks).Execution) : Prop where
  aligned : execution.network.ledger.length = execution.receipts.length
  finished : ∀ event id, runtime.acceptedFor leaks execution event id →
    event ∈ execution.application.config.cut.completed
  unique : ∀ event first second, runtime.acceptedFor leaks execution event first →
    runtime.acceptedFor leaks execution event second → first = second
  addressed : ∀ id, (id, true) ∈ execution.receipts →
    ∃ event, runtime.acceptedFor leaks execution event id
  owned : ∀ event id, runtime.acceptedFor leaks execution event id →
    graph.actor? event = some id.1

omit [DecidableEq Player] in
private theorem acceptedFor_append
    (ledger : List (Message Player (WitnessedPacket graph)))
    (receipts : List (MessageId Player × Bool))
    (aligned : ledger.length = receipts.length)
    (message : Message Player (WitnessedPacket graph)) (id : MessageId Player)
    (success : Bool) (event : graph.EventId) (other : MessageId Player) :
    (∃ packet, (packet, (other, true)) ∈
      (ledger ++ [message]).zip (receipts ++ [(id, success)]) ∧
        packet.payload.call.event? graph = some event) ↔
      (∃ packet, (packet, (other, true)) ∈ ledger.zip receipts ∧
        packet.payload.call.event? graph = some event) ∨
      (other = id ∧ success = true ∧ message.payload.call.event? graph = some event) := by
  rw [List.zip_append aligned]
  simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨packet, old | fresh, named⟩
    · exact Or.inl ⟨packet, old, named⟩
    · obtain ⟨rfl, equal⟩ := Prod.mk.inj fresh
      exact Or.inr ⟨(Prod.mk.inj equal).1, (Prod.mk.inj equal).2.symm, named⟩
  · rintro (⟨packet, member, named⟩ | ⟨rfl, rfl, named⟩)
    · exact ⟨packet, Or.inl member, named⟩
    · exact ⟨message, Or.inr rfl, named⟩

private theorem acceptanceUnique_copy
    (before after : (runtime.reactiveApplication leaks).Execution)
    (valid : runtime.AcceptanceUnique leaks before)
    (ledger : after.network.ledger = before.network.ledger)
    (receipts : after.receipts = before.receipts)
    (completed : before.application.config.cut.completed ⊆
      after.application.config.cut.completed) : runtime.AcceptanceUnique leaks after := by
  have same (event : graph.EventId) (id : MessageId Player) :
      runtime.acceptedFor leaks after event id ↔ runtime.acceptedFor leaks before event id := by
    simp only [acceptedFor, ledger, receipts]
  refine ⟨by rw [ledger, receipts]; exact valid.aligned, ?_, ?_, ?_, ?_⟩
  · intro event id accepted
    exact completed (valid.finished event id ((same event id).mp accepted))
  · intro event first second one two
    exact valid.unique event first second ((same event first).mp one) ((same event second).mp two)
  · intro id accepted
    rw [receipts] at accepted
    obtain ⟨event, named⟩ := valid.addressed id accepted
    exact ⟨event, (same event id).mpr named⟩
  · intro event id accepted
    exact valid.owned event id ((same event id).mp accepted)

private theorem acceptanceUnique_initial (state : State graph) :
    runtime.AcceptanceUnique leaks
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state) where
  aligned := rfl
  finished := by rintro _ _ ⟨_, impossible, _⟩; cases impossible
  unique := by rintro _ _ _ ⟨_, impossible, _⟩; cases impossible
  addressed := by intro _ impossible; cases impossible
  owned := by rintro _ _ ⟨_, impossible, _⟩; cases impossible

private theorem acceptanceUnique_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action)
    (valid : runtime.AcceptanceUnique leaks execution) :
    runtime.AcceptanceUnique leaks
      (execution.respond (runtime.reactiveApplication leaks) who action) := by
  have ledger := (runtime.reactiveApplication leaks).respond_ledger execution who action
  have receipts := (runtime.reactiveApplication leaks).respond_receipts execution who action
  have physical := (runtime.reactive_respond_application leaks execution who action).1
  apply runtime.acceptanceUnique_copy leaks _ _ valid ledger receipts
  rw [physical]

private theorem acceptanceUnique_include
    (execution : (runtime.reactiveApplication leaks).Execution) (id : MessageId Player)
    (valid : runtime.AcceptanceUnique leaks execution) :
    runtime.AcceptanceUnique leaks
      (execution.includePending (runtime.reactiveApplication leaks) id) := by
  cases found : execution.network.lookup id with
  | none =>
      simpa only [ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, found] using valid
  | some message =>
      cases handled : (runtime.reactiveApplication leaks).handle execution.application message with
      | none =>
          have classified (event : graph.EventId) (other : MessageId Player) :
              runtime.acceptedFor leaks
                (execution.includePending (runtime.reactiveApplication leaks) id) event other ↔
                  runtime.acceptedFor leaks execution event other := by
            unfold acceptedFor ReactiveApplication.Execution.includePending
            simp only [MessageNetwork.includePending, found, handled]
            exact (acceptedFor_append _ _ valid.aligned message id false event other).trans
              (by simp; rfl)
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · unfold ReactiveApplication.Execution.includePending
            simp only [MessageNetwork.includePending, found, handled]
            simpa only [List.length_append, List.length_singleton] using
              congrArg Nat.succ valid.aligned
          · intro event other accepted
            have old := valid.finished event other ((classified event other).mp accepted)
            simpa only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found, handled, Option.getD_none] using old
          · intro event first second one two
            exact valid.unique event first second
              ((classified event first).mp one) ((classified event second).mp two)
          · intro other accepted
            have old : (other, true) ∈ execution.receipts := by
              simpa only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, handled, Option.isSome_none,
                List.mem_append, List.mem_singleton, Prod.mk.injEq, Bool.true_eq_false,
                and_false, or_false] using accepted
            obtain ⟨event, addressed⟩ := valid.addressed other old
            exact ⟨event, (classified event other).mpr addressed⟩
          · intro event other accepted
            exact valid.owned event other ((classified event other).mp accepted)
      | some physical =>
          obtain ⟨event, named, unfinished, finished⟩ := handle_completes runtime
            execution.application physical ⟨message.id, message.payload.call⟩
              (reactiveHandle_call handled)
          change message.payload.call.event? graph = some event at named
          have monotone := handle_completed_subset runtime execution.application physical
            ⟨message.id, message.payload.call⟩ (reactiveHandle_call handled)
          obtain ⟨ownedEvent, ownedNamed, ownedActor⟩ := handle_event_actor runtime
            execution.application physical ⟨message.id, message.payload.call⟩
              (reactiveHandle_call handled)
          have eventEq : ownedEvent = event := Option.some.inj (ownedNamed.symm.trans named)
          have identified : message.id = id := by
            simpa only [decide_eq_true_eq] using List.find?_some found
          have owner : graph.actor? event = some id.1 := by
            rw [← eventEq]
            simpa only [Message.sender, identified] using ownedActor
          have classified (query : graph.EventId) (other : MessageId Player) :
              runtime.acceptedFor leaks
                (execution.includePending (runtime.reactiveApplication leaks) id) query other ↔
                  runtime.acceptedFor leaks execution query other ∨
                    (other = id ∧ query = event) := by
            unfold acceptedFor ReactiveApplication.Execution.includePending
            simp only [MessageNetwork.includePending, found, handled, Option.isSome_some]
            refine (acceptedFor_append _ _ valid.aligned message id true query other).trans ?_
            rw [named]
            simp only [true_and, Option.some.injEq, eq_comm]
            rfl
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · unfold ReactiveApplication.Execution.includePending
            simp only [MessageNetwork.includePending, found, handled]
            simpa only [List.length_append, List.length_singleton] using
              congrArg Nat.succ valid.aligned
          · intro query other accepted
            have done : query ∈ physical.config.cut.completed := by
              rcases (classified query other).mp accepted with old | ⟨_, rfl⟩
              · exact monotone (valid.finished query other old)
              · exact finished
            simpa only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found, handled, Option.getD_some] using done
          · intro query first second one two
            rcases (classified query first).mp one with oldOne | ⟨rfl, sameOne⟩
            · rcases (classified query second).mp two with oldTwo | ⟨rfl, sameTwo⟩
              · exact valid.unique query first second oldOne oldTwo
              · exact (unfinished (sameTwo ▸ valid.finished query first oldOne)).elim
            · rcases (classified query second).mp two with oldTwo | ⟨rfl, _⟩
              · exact (unfinished (sameOne ▸ valid.finished query second oldTwo)).elim
              · rfl
          · intro other accepted
            have located : (other, true) ∈ execution.receipts ∨ other = id := by
              simpa only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, handled, Option.isSome_some,
                List.mem_append, List.mem_singleton, Prod.mk.injEq, and_true] using accepted
            rcases located with old | rfl
            · obtain ⟨query, addressed⟩ := valid.addressed other old
              exact ⟨query, (classified query other).mpr (Or.inl addressed)⟩
            · exact ⟨event, (classified event other).mpr (Or.inr ⟨rfl, rfl⟩)⟩
          · intro query other accepted
            rcases (classified query other).mp accepted with old | ⟨rfl, rfl⟩
            · exact valid.owned query other old
            · exact owner

private theorem acceptanceUnique_environment
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (valid : runtime.AcceptanceUnique leaks execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.AcceptanceUnique leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact runtime.acceptanceUnique_copy leaks _ _ valid rfl rfl (Finset.Subset.refl _)
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact runtime.acceptanceUnique_copy leaks _ _ valid rfl rfl (Finset.Subset.refl _)
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact runtime.acceptanceUnique_copy leaks _ _
        (runtime.acceptanceUnique_include leaks execution id valid) rfl rfl (Finset.Subset.refl _)
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      change updated ∈ ((environmentStep runtime execution.application command).map
        (fun physical => { execution with application := physical })).support at supported
      obtain ⟨physical, moved, rfl⟩ := PMF.support_map .. ▸ supported
      exact runtime.acceptanceUnique_copy leaks _ _ valid rfl rfl
        (environmentStep_completed_subset runtime execution.application physical command moved)

theorem acceptanceUniqueInvariant
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (runtime.AcceptanceUnique leaks) where
  respond := runtime.acceptanceUnique_respond leaks
  environment execution next command valid _ reached :=
    runtime.acceptanceUnique_environment leaks execution next command valid reached

theorem acceptanceUnique_history
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.serviceInvariant (runtime.AcceptanceUnique leaks) state :=
  (runtime.acceptanceUniqueInvariant leaks scheduler).history initial horizon
    (fun state _ => runtime.acceptanceUnique_initial leaks state) trace

/-- Two actual accepting ledger/receipt pairs for the same event have the
same message identifier. No restriction on raw submissions is used. -/
theorem accepting_identifiers_unique
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (event : graph.EventId) (first second : MessageId Player)
    (one : runtime.acceptedFor leaks control.execution event first)
    (two : runtime.acceptedFor leaks control.execution event second) : first = second :=
  (runtime.acceptanceUnique_history leaks initial horizon scheduler trace).unique
    event first second one two

/-- An actual accepting receipt identifies an owned completed event and a
matching ledger envelope. The sender is certified by the handler. -/
theorem accepting_receipt_has_owned_event
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (id : MessageId Player)
    (accepted : (id, true) ∈ control.execution.receipts) :
    ∃ event, runtime.acceptedFor leaks control.execution event id ∧
      graph.actor? event = some id.1 ∧
        event ∈ control.execution.application.config.cut.completed := by
  have valid := runtime.acceptanceUnique_history leaks initial horizon scheduler trace
  obtain ⟨event, addressed⟩ := valid.addressed id accepted
  exact ⟨event, addressed, valid.owned event id addressed, valid.finished event id addressed⟩

end Vegas.EventGraphRuntime
