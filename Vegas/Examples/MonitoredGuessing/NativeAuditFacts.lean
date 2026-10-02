/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativePrelude
import Vegas.Examples.MonitoredGuessing.NativeLiability
import Vegas.Pending.EventOpponentFrame
import Vegas.Pending.ReactiveServiceAudit
import Interaction.ReactiveMessageIdentity

/-! # Authentic packet marks and completed-record verdicts -/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def NativeReceipts (execution : nativeApp.Execution) : Prop :=
  List.Forall₂ (fun message receipt => receipt.1 = message.id ∧
    (receipt.2 = true → message.sender = alice → prematureAlicePacket message.payload = false))
    execution.network.ledger execution.receipts

theorem native_accepted_nonpremature (state next : EventGraphRuntime.State nativeGraph)
    (message : Message Player (WitnessedPacket nativeGraph))
    (handled : nativeApp.handle state message = some next) (sender : message.sender = alice) :
    prematureAlicePacket message.payload = false := by
  obtain ⟨token, call⟩ := reactiveApplication_handle_eq_some nativeRuntime nativeLeaks
    state next message handled
  obtain ⟨event, named, actor⟩ := nativeRuntime.handle_event_actor state next
    ⟨message.id, message.payload.call⟩ call
  have owner : event = alicePublication := by
    rw [native_actor] at actor
    change some (nativeOwner event) = some message.sender at actor
    rw [sender] at actor
    fin_cases event <;> simp_all [nativeOwner, bobPublication, alicePublication, bob, alice]
  cases packet : message.payload.call with
  | opening addressed candidate raw | withhold addressed =>
      have same : addressed = event := by simpa only [packet, Payload.event?, Option.some.injEq]
        using named
      rw [prematureAlicePacket, packet, same, owner, token]
      rfl
  | malformed raw => simp [packet, handle] at call
  | commitment addressed candidate =>
      have same : addressed = event := by
        simpa only [packet, Payload.event?, Option.some.injEq] using named
      rw [packet, same, owner] at call
      dsimp only [handle] at call
      split at call
      · split at call
        · rw [alice_node] at call
          cases call
        · cases call
      · cases call

theorem nativeReceipts_include (execution : nativeApp.Execution) (id : MessageId Player)
    (facts : NativeReceipts execution) : NativeReceipts (execution.includePending nativeApp id)
      := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact facts
  | some message =>
      have identified : message.id = id := by
        simpa using (List.find?_eq_some_iff_append.mp found).1
      apply List.rel_append facts
      refine List.Forall₂.cons ⟨identified.symm, ?_⟩ List.Forall₂.nil
      intro accepted sender
      obtain ⟨next, handled⟩ := Option.isSome_iff_exists.mp accepted
      exact native_accepted_nonpremature execution.application next message handled sender

theorem nativeReceipts_invariant (scheduler : nativeApp.Scheduler) :
    nativeApp.ServiceInvariant scheduler NativeReceipts where
  respond execution who action facts := by
    rcases action with ⟨transmission⟩
    cases transmission <;> exact facts
  environment execution next command facts _ reached := by
    cases command with
    | activate who =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact facts
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact facts
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact nativeReceipts_include execution id facts
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact facts

theorem nativeReceipts_history (control : nativeApp.Control)
    (trace : (nativeApp.protocol nativeInitialLaw nativeHorizon nativeScheduler).Trace
      (some control)) : NativeReceipts control.execution :=
  (nativeReceipts_invariant nativeScheduler).history nativeInitialLaw nativeHorizon
    (fun _ _ => List.Forall₂.nil) trace

theorem NativeReceipts.receipt_witness {execution : nativeApp.Execution}
    (facts : NativeReceipts execution) {receipt : MessageId Player × Bool}
    (present : receipt ∈ execution.receipts) :
    ∃ message ∈ execution.network.ledger, receipt.1 = message.id ∧
      (receipt.2 = true → message.sender = alice → prematureAlicePacket message.payload =
        false) := by
  unfold NativeReceipts at facts
  generalize execution.network.ledger = ledger at facts ⊢
  generalize execution.receipts = receipts at facts present
  induction facts with
  | nil => cases present
  | @cons message receipt messages receipts related facts ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨message, List.mem_cons_self .., related⟩
      · obtain ⟨message, member, related⟩ := ih later
        exact ⟨message, List.mem_cons_of_mem _ member, related⟩

theorem NativeReceipts.ledger_witness {execution : nativeApp.Execution}
    (facts : NativeReceipts execution) {message : Message Player (WitnessedPacket nativeGraph)}
    (present : message ∈ execution.network.ledger) :
    ∃ receipt ∈ execution.receipts, receipt.1 = message.id ∧
      (receipt.2 = true → message.sender = alice → prematureAlicePacket message.payload =
        false) := by
  unfold NativeReceipts at facts
  generalize execution.network.ledger = ledger at facts present
  generalize execution.receipts = receipts at facts ⊢
  induction facts with
  | nil => cases present
  | @cons message receipt messages receipts related facts ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨receipt, List.mem_cons_self .., related⟩
      · obtain ⟨receipt, member, related⟩ := ih later
        exact ⟨receipt, List.mem_cons_of_mem _ member, related⟩

theorem NativeReceipts.ids {execution : nativeApp.Execution} (facts : NativeReceipts execution) :
    execution.receipts.map Prod.fst = execution.network.ledger.map Message.id := by
  unfold NativeReceipts at facts
  generalize execution.network.ledger = ledger at facts ⊢
  generalize execution.receipts = receipts at facts ⊢
  induction facts with
  | nil => rfl
  | cons related _ ih => simp only [List.map_cons, related.1, ih]

def nativeAuditPackets (execution : nativeApp.Execution) :
    List (Message Player (WitnessedPacket nativeGraph)) :=
  execution.network.ledger ++ execution.network.leaked watcher

open Classical in
def nativeAuditEligible (execution : nativeApp.Execution)
    (message : Message Player (WitnessedPacket nativeGraph)) : Bool :=
  decide (message.sender = alice ∧
    ((message.id, false) ∈ execution.receipts ∨ prematureAlicePacket message.payload = true))

def nativeAuditVerdict (execution : nativeApp.Execution)
    (message : Message Player (WitnessedPacket nativeGraph)) : Bool :=
  nativeAuditEligible execution message &&
    !((nativeRuntime.settledRecord nativeLeaks execution).permits message)

theorem nativeAuditVerdict_of_eligible (execution : nativeApp.Execution)
    (facts : NativeReceipts execution) (unique : execution.network.UniqueIds)
    (once : execution.network.PublishedOnce)
    (complete : execution.application.config.cut.Terminal)
    (message : Message Player (WitnessedPacket nativeGraph))
    (observed : message ∈ nativeAuditPackets execution)
    (eligible : nativeAuditEligible execution message = true) :
    nativeAuditVerdict execution message = true := by
  have classified : message.sender = alice ∧
      ((message.id, false) ∈ execution.receipts ∨ prematureAlicePacket message.payload = true) :=
    of_decide_eq_true eligible
  have unaccepted : (message.id, true) ∉ execution.receipts := by
    intro accepted
    rcases classified.2 with rejected | premature
    · have ids : (execution.receipts.map Prod.fst).Nodup := by
        rw [facts.ids]
        exact once
      have same := List.inj_on_of_nodup_map ids rejected accepted rfl
      have impossible := congrArg Prod.snd same
      cases impossible
    · obtain ⟨witness, published, identified, checked⟩ := facts.receipt_witness accepted
      have same : message = witness := by
        rcases List.mem_append.mp observed with recorded | leaked
        · exact (unique.ledger witness published).ledger message recorded identified
        · exact (unique.ledger witness published).leaked watcher message leaked identified
      have good := checked rfl (same ▸ classified.1)
      rw [← same, premature] at good
      cases good
  have forbidden : (nativeRuntime.settledRecord nativeLeaks execution).permits message = false := by
    cases address : message.payload.call.event? nativeGraph with
    | none => exact SettledRecord.permits_eq_false_of_none _ message address
    | some event =>
        have settled : event ∈
            (nativeRuntime.settledRecord nativeLeaks
              execution).view.observation.completionOrder := by
          apply (execution.application.config.history_exact event).mpr
          rw [complete]
          exact Finset.mem_univ event
        exact SettledRecord.permits_eq_false_of_settled _ message event address settled
          (fun accepted => unaccepted accepted.1)
  simp only [nativeAuditVerdict, eligible, forbidden, Bool.not_false, Bool.and_self]

theorem nativeAuditEligible_iff_liability (execution : nativeApp.Execution)
    (facts : NativeReceipts execution) :
    (nativeAuditPackets execution).any (nativeAuditEligible execution) = aliceLiability
      execution := by
  have forward : (nativeAuditPackets execution).any (nativeAuditEligible execution) = true →
      aliceLiability execution = true := by
    intro found
    obtain ⟨message, observed, eligible⟩ := List.any_eq_true.mp found
    have classified : message.sender = alice ∧
        ((message.id, false) ∈ execution.receipts ∨ prematureAlicePacket message.payload = true) :=
      of_decide_eq_true eligible
    simp only [aliceLiability, Bool.or_eq_true]
    rcases classified.2 with rejected | premature
    · left
      apply List.any_eq_true.mpr
      exact ⟨(message.id, false), rejected, by
        have owner : message.id.1 = alice := classified.1
        simp only [owner, decide_true, Bool.not_false, Bool.true_and]⟩
    · rcases List.mem_append.mp observed with recorded | leaked
      · left
        obtain ⟨receipt, present, identified, checked⟩ := facts.ledger_witness recorded
        have rejected : receipt.2 = false := by
          cases status : receipt.2 with
          | false => rfl
          | true => have good := checked status classified.1; rw [premature] at good; cases good
        apply List.any_eq_true.mpr
        exact ⟨receipt, present, by simp [identified, rejected, ← classified.1, Message.sender]⟩
      · right
        apply List.any_eq_true.mpr
        exact ⟨message, leaked, by simp [classified.1, premature]⟩
  have backward : aliceLiability execution = true →
      (nativeAuditPackets execution).any (nativeAuditEligible execution) = true := by
    intro liable
    simp only [aliceLiability, Bool.or_eq_true] at liable
    rcases liable with rejected | premature
    · obtain ⟨receipt, present, flagged⟩ := List.any_eq_true.mp rejected
      have identified : receipt.1.1 = alice ∧ receipt.2 = false := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true_eq_eq_false] using flagged
      obtain ⟨message, recorded, same, _⟩ := facts.receipt_witness present
      apply List.any_eq_true.mpr
      refine ⟨message, List.mem_append_left _ recorded, ?_⟩
      apply decide_eq_true
      refine ⟨by simpa only [Message.sender, ← same] using identified.1, Or.inl ?_⟩
      have pair : receipt = (message.id, false) := Prod.ext same identified.2
      exact pair ▸ present
    · obtain ⟨message, leaked, flagged⟩ := List.any_eq_true.mp premature
      have classified : message.sender = alice ∧ prematureAlicePacket message.payload = true := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using flagged
      apply List.any_eq_true.mpr
      exact ⟨message, List.mem_append_right _ leaked, decide_eq_true
        ⟨classified.1, Or.inr classified.2⟩⟩
  exact Bool.eq_iff_iff.mpr ⟨forward, backward⟩

theorem nativeAuditVerdict_eq_liability (execution : nativeApp.Execution)
    (facts : NativeReceipts execution) (unique : execution.network.UniqueIds)
    (once : execution.network.PublishedOnce)
    (complete : execution.application.config.cut.Terminal) :
    (nativeAuditPackets execution).any (nativeAuditVerdict execution) = aliceLiability
      execution := by
  rw [← nativeAuditEligible_iff_liability execution facts]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro found
    obtain ⟨message, present, verdict⟩ := List.any_eq_true.mp found
    simp only [nativeAuditVerdict, Bool.and_eq_true] at verdict
    exact List.any_eq_true.mpr ⟨message, present, verdict.1⟩
  · intro found
    obtain ⟨message, present, eligible⟩ := List.any_eq_true.mp found
    exact List.any_eq_true.mpr ⟨message, present,
      nativeAuditVerdict_of_eligible execution facts unique once complete message present eligible⟩

end Vegas.Examples.MonitoredGuessing
