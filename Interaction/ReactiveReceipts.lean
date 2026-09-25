/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveHistory

/-! # Public receipts certify payload properties

The ledger and receipt list advance together. A property checked by every
successful application call therefore remains attached to its public packet,
under arbitrary submissions, replay, passive observation and scheduling.
Receipts also persist along every legal continuation, including rejected calls.
This preserves evidence; it does not implement collection of a financial claim.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem respond_receipts (execution : app.Execution) (who : Principal)
    (action : app.Action) :
    (execution.respond app who action).receipts = execution.receipts := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material => rfl
      | replay id =>
          cases found : (execution.network.known who).find? (fun envelope => envelope.id = id) <;>
            simp only [Execution.respond, MessageNetwork.replay, found]

theorem includePending_receipts_prefix (execution : app.Execution)
    (id : MessageId Principal) :
    execution.receipts <+: (execution.includePending app id).receipts := by
  unfold Execution.includePending MessageNetwork.includePending
  cases execution.network.lookup id with
  | none => rfl
  | some message => exact ⟨_, rfl⟩

theorem environmentStep_receipts_prefix (execution next : app.Execution)
    (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    execution.receipts <+: next.receipts := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact app.includePending_receipts_prefix execution id
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      rfl

theorem transition_receipts_prefix (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before : app.Control) (after : app.ProtocolState)
    (joint : Principal → Option app.Action)
    (reached : after ∈ (app.transition initial horizon scheduler (some before) joint).support) :
    ∃ next, after = some next ∧ before.execution.receipts <+: next.execution.receipts := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      cases FinDist.mem_support_pure.mp reached
      refine ⟨_, rfl, ?_⟩
      rw [app.respond_receipts]
  | none =>
      cases remaining with
      | zero => cases FinDist.mem_support_pure.mp reached; exact ⟨_, rfl, by rfl⟩
      | succ remaining =>
          obtain ⟨command, _, supported⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
          obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
          exact ⟨_, rfl, app.environmentStep_receipts_prefix execution next command moved⟩

/-- A later response, timeout or inclusion cannot erase an existing receipt.
The history may start after arbitrary prior deviations. -/
theorem reaches_receipts_prefix (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last)
    (before after : app.Control) (firstEq : first.state = some before)
    (lastEq : last.state = some after) :
    before.execution.receipts <+: after.execution.receipts := by
  induction path generalizing before with
  | refl _ history => cases Option.some.inj (firstEq.symm.trans lastEq); rfl
  | @step steps history target joint legal reached supported suffix ih =>
      have moved := supported
      change reached ∈ (app.transition initial horizon scheduler history.state joint).support
        at moved
      rw [firstEq] at moved
      obtain ⟨middle, middleEq, retained⟩ := app.transition_receipts_prefix
        initial horizon scheduler before reached joint moved
      exact retained.trans (ih middle middleEq lastEq)

def Execution.ReceiptsSound (predicate : app.Payload → Prop) (execution : app.Execution) : Prop :=
  List.Forall₂ (fun message receipt => receipt.1 = message.id ∧
    (receipt.2 = true → predicate message.payload)) execution.network.ledger execution.receipts

omit [DecidableEq Principal] in
/-- Evidence extracted from the public ledger and its corresponding receipt. -/
theorem Execution.ReceiptsSound.certifies (predicate : app.Payload → Prop)
    (execution : app.Execution) (sound : execution.ReceiptsSound app predicate)
    (message : Message Principal app.Payload) (id : MessageId Principal)
    (accepted : (message, (id, true)) ∈ execution.network.ledger.zip execution.receipts) :
    predicate message.payload :=
  (List.forall₂_zip sound accepted).2 rfl

omit [DecidableEq Principal] in
theorem receiptsSound_initial (predicate : app.Payload → Prop) (state : app.State) :
    (Execution.initial app state).ReceiptsSound app predicate := List.Forall₂.nil

theorem receiptsSound_respond (predicate : app.Payload → Prop)
    (execution : app.Execution) (who : Principal) (action : app.Action)
    (sound : execution.ReceiptsSound app predicate) :
    (execution.respond app who action).ReceiptsSound app predicate := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact sound
  | some transmission =>
      cases transmission with
      | submit material => exact sound
      | replay id =>
          cases found : (execution.network.known who).find? (fun envelope => envelope.id = id) <;>
            simpa only [Execution.respond, MessageNetwork.replay, found,
              Execution.ReceiptsSound] using sound

theorem receiptsSound_includePending (predicate : app.Payload → Prop)
    (execution : app.Execution) (id : MessageId Principal)
    (sound : execution.ReceiptsSound app predicate)
    (checked : ∀ message next, app.handle execution.application message = some next →
      predicate message.payload) :
    (execution.includePending app id).ReceiptsSound app predicate := by
  unfold Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact sound
  | some message =>
      have addressed : message.id = id := by
        have identified := (List.find?_eq_some_iff_append.mp found).1
        simpa only [decide_eq_true_eq] using identified
      change List.Forall₂ _ (execution.network.ledger ++ [message])
        (execution.receipts ++ [(id, (app.handle execution.application message).isSome)])
      have last : List.Forall₂ (fun message receipt => receipt.1 = message.id ∧
          (receipt.2 = true → predicate message.payload)) [message]
          [(id, (app.handle execution.application message).isSome)] := by
        refine List.Forall₂.cons ⟨addressed.symm, ?_⟩ List.Forall₂.nil
        intro accepted
        obtain ⟨next, same⟩ := Option.isSome_iff_exists.mp accepted
        exact checked message next same
      exact List.rel_append sound last

theorem receiptsSound_environmentStep (predicate : app.Payload → Prop)
    (execution next : app.Execution) (command : app.Command)
    (sound : execution.ReceiptsSound app predicate)
    (checked : ∀ message next, app.handle execution.application message = some next →
      predicate message.payload)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.ReceiptsSound app predicate := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact sound
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact sound
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact app.receiptsSound_includePending predicate execution id sound checked
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact sound

theorem receiptServiceInvariant (statePredicate : app.State → Prop)
    (payloadPredicate : app.Payload → Prop) (invariant : app.Invariant statePredicate)
    (checked : ∀ state message next, statePredicate state →
      app.handle state message = some next → payloadPredicate message.payload)
    (scheduler : app.Scheduler) : app.ServiceInvariant scheduler
      (fun execution => statePredicate execution.application ∧
        execution.ReceiptsSound app payloadPredicate) where
  respond execution who action valid :=
    ⟨invariant.respond execution who action valid.1,
      app.receiptsSound_respond payloadPredicate execution who action valid.2⟩
  environment execution next command valid _ reached :=
    ⟨invariant.environmentStep execution next command valid.1 reached,
      app.receiptsSound_environmentStep payloadPredicate execution next command valid.2
        (fun message final => checked execution.application message final valid.1) reached⟩

end Interaction.ReactiveApplication
