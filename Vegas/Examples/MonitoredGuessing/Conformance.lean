/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeHonest
import Vegas.Pending.ReactiveConformance
import Vegas.Pending.ReactiveSelectionObservation
import Interaction.ReactiveLedgerConformance

/-! # Accepted extra evidence is visible without triggering the pilot's charge

The complete raw menu permits an owner to attach an authentic opening certificate
to an ordinary withholding call. The application accepts the call, while the
ledger retains the extra certificate. This is an operational coverage test for
conformance enforcement, not a sequential-equilibrium impossibility theorem.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Conformance

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def certifiedWithholding : WitnessedSubmission nativeGraph :=
  ⟨⟨.withhold bobPublication, none⟩, .owned ⟨bobHandle, ⟨.bool, true⟩⟩⟩

def certifiedWithholdAction : nativeApp.Action := ⟨some (.submit certifiedWithholding)⟩

def certifiedWithholdRespond (bit : Bool) : nativeApp.Execution :=
  (quietBob bit).respond nativeApp bob certifiedWithholdAction

def certifiedWithholdIncluded (bit : Bool) : nativeApp.Execution :=
  let before := certifiedWithholdRespond bit
  { before.includePending nativeApp (bob, 0) with
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .include (bob, 0)⟩] }

theorem certified_withholding_available (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) :
    certifiedWithholdAction ∈ nativeMenu.actions bob past view := by
  change certifiedWithholdAction ∈
    (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions bob past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change certifiedWithholding ∈ _
  rw [MessageBounds.submissions_mem]
  exact ⟨⟨trivial, trivial⟩, trivial, by decide⟩

theorem certified_withholding_emits (bit : Bool)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    certifiedWithholding.emit (quietBob bit).application bob known =
      ⟨.withhold bobPublication, some ⟨bobHandle, ⟨.bool, true⟩⟩, some ⟨bobPublication⟩⟩ := by
  have valid : (⟨bobHandle, ⟨.bool, true⟩⟩ : OpeningFact nativeGraph).Holds
      (quietBob bit).application := (quiet_bob_fixed bit).bob_candidate
  have evidence := WitnessedSubmission.emit_owned
    (⟨.withhold bobPublication, none⟩ : Submission nativeGraph)
    (quietBob bit).application bob known ⟨bobHandle, ⟨.bool, true⟩⟩ rfl valid
  have token := quiet_bob_token bit (.withhold bobPublication) rfl
  change WitnessedPacket.mk _ _
    ((quietBob bit).application.publicView.tokenFor (.withhold bobPublication)) = _
  rw [token]
  exact congrArg (fun evidence => WitnessedPacket.mk (.withhold bobPublication) evidence
    (some ⟨bobPublication⟩)) evidence

theorem certified_withholding_included (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob) (certifiedWithholdRespond bit) =
        PMF.pure (certifiedWithholdIncluded bit) := by
  have selected : nativeRuntime.reactiveLatest nativeLeaks bobPublication bob
      ((certifiedWithholdRespond bit).observeEnvironment nativeApp) = .include (bob, 0) := by
    simpa only [certifiedWithholdRespond, certifiedWithholdAction,
      quiet_bob_network, MessageNetwork.empty] using
      nativeRuntime.reactiveLatest_after_submit nativeLeaks bob bobPublication
        (quietBob bit) (quiet_bob_serials bit) certifiedWithholding rfl
  rw [nativeRuntime.interaction_includeLatest_environment, selected]
  change (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  rfl

theorem certified_withholding_application (bit : Bool) :
    (certifiedWithholdIncluded bit).application = (quietGuessIncluded bit false).application ∧
      (certifiedWithholdIncluded bit).receipts = [((bob, 0), true)] := by
  obtain ⟨next, accepted, _, applicationEq, _⟩ := quiet_guess_application bit false
  have law := resolution_submission_inclusion (fun _ => nativeAlicePolicy)
    (quietBob bit) bob bobPublication certifiedWithholding next (quiet_bob_serials bit)
    rfl rfl (by simpa only [certifiedWithholding, quiet_bob_network,
      MessageNetwork.empty, Bool.false_eq_true, ↓reduceIte] using accepted)
  change (nativeRuntime.interactionStep nativeLeaks (fun _ => nativeAlicePolicy) nativeNetwork
    (.includeLatest bobPublication bob) (certifiedWithholdRespond bit)).map
    (fun result => (result.application, result.receipts)) = _ at law
  rw [certified_withholding_included, PMF.pure_map] at law
  have pair := (PMF.mem_support_pure_iff _ _).mp (law ▸ (PMF.mem_support_pure_iff _ _).mpr rfl)
  constructor
  · exact (congrArg Prod.fst pair).trans applicationEq.symm
  · exact congrArg Prod.snd pair

theorem certified_withholding_public_failure (bit : Bool) :
    bobPublicationRef.get? (certifiedWithholdIncluded bit).application.config.store =
      some .failure := by
  rw [(certified_withholding_application bit).1]
  exact (quiet_guess_results bit false).1

theorem certified_withholding_network (bit : Bool) :
    (certifiedWithholdRespond bit).network =
      (MessageNetwork.empty.submit bob
        (⟨.withhold bobPublication, some ⟨bobHandle, ⟨.bool, true⟩⟩, some ⟨bobPublication⟩⟩ :
          WitnessedPacket nativeGraph)).2 := by
  change ((quietBob bit).network.submit bob
    (certifiedWithholding.emit (quietBob bit).application bob
      ((quietBob bit).network.known bob))).2 = _
  rw [certified_withholding_emits, quiet_bob_network]

theorem certified_withholding_ledger (bit : Bool) :
    (certifiedWithholdIncluded bit).network.ledger =
      [⟨(bob, 0), ⟨.withhold bobPublication, some ⟨bobHandle, ⟨.bool, true⟩⟩,
        some ⟨bobPublication⟩⟩⟩] := by
  change ((certifiedWithholdRespond bit).includePending nativeApp (bob, 0)).network.ledger = _
  rw [nativeApp.includePending_network, certified_withholding_network]
  simp [MessageNetwork.includePending, MessageNetwork.lookup, MessageNetwork.submit,
    MessageNetwork.empty]

theorem canonical_withholding_ledger (bit : Bool) :
    (quietGuessIncluded bit false).network.ledger =
      [⟨(bob, 0), ⟨.withhold bobPublication, none, some ⟨bobPublication⟩⟩⟩] := by
  change ((quietGuessRespond bit false).includePending nativeApp (bob, 0)).network.ledger = _
  rw [nativeApp.includePending_network]
  change (((quietBob bit).network.submit bob
    (⟨.withhold bobPublication, none,
      (quietBob bit).application.publicView.tokenFor (.withhold bobPublication)⟩ :
        WitnessedPacket nativeGraph)).2.includePending (bob, 0)).2.ledger = _
  rw [quiet_bob_network, quiet_bob_token bit (.withhold bobPublication) rfl]
  simp [MessageNetwork.includePending, MessageNetwork.lookup, MessageNetwork.submit,
    MessageNetwork.empty]

theorem extra_evidence_changes_alice_observation (bit : Bool) :
    (certifiedWithholdIncluded bit).observe nativeApp alice ≠
      (quietGuessIncluded bit false).observe nativeApp alice := by
  intro same
  have ledger := congrArg (fun view : nativeApp.PlayerView =>
    view.messages.ledger.map (fun message => message.payload.evidence)) same
  change (certifiedWithholdIncluded bit).network.ledger.map _ =
    (quietGuessIncluded bit false).network.ledger.map _ at ledger
  rw [certified_withholding_ledger, canonical_withholding_ledger] at ledger
  simp at ledger

theorem accepted_packet_is_nonconforming (bit : Bool) :
    ((certifiedWithholdIncluded bit).network.ledger.map
      (fun message => unsupportedEvidence message.payload)) = [true] := by
  rw [certified_withholding_ledger]
  rfl

theorem accepted_packet_creates_no_pilot_liability (bit : Bool) :
    rejectedAlice (certifiedWithholdIncluded bit).receipts = false := by
  rw [(certified_withholding_application bit).2]
  rfl

/-- The pilot has no receiver charge, even at histories with other receipts. -/
theorem bob_uncharged (deposit : ℝ) (execution : nativeApp.Execution) :
    nativeExecutionUtility deposit bob execution =
      utility (nativeResults execution.application.config) bob := by
  simp [nativeExecutionUtility, bob, alice]

/-- Successful opening keeps the matching certificate used by the actual pilot
and the generic compiler. The candidate withholding implementation is silence
followed by expiry. Removing an opening's certificate changes its public packet;
it is not a private representation alias. This checker cannot establish when a
pending packet was transmitted. -/
def bobPacketPermitted (packet : WitnessedPacket nativeGraph) : Bool :=
  match packet.call, packet.evidence with
  | .opening event candidate raw, some fact =>
      decide (event = bobPublication ∧ candidate = bobHandle ∧ raw = ⟨.bool, true⟩ ∧
        fact = ⟨candidate, raw⟩ ∧ packet.token = some ⟨bobPublication⟩)
  | _, _ => false

def bobLedgerViolation (execution : nativeApp.Execution) : Bool :=
  ledgerViolation bob bobPacketPermitted execution.network.ledger

/-- A unit liability score, not a proof that funds have been collected. -/
def bobLedgerLiability (execution : nativeApp.Execution) : ℝ :=
  if bobLedgerViolation execution then 1 else 0

theorem certified_withholding_detected (bit : Bool) :
    bobLedgerViolation (certifiedWithholdIncluded bit) = true := by
  rw [bobLedgerViolation, certified_withholding_ledger]
  rfl

theorem certified_withholding_liability (bit : Bool) :
    bobLedgerLiability (certifiedWithholdIncluded bit) = 1 := by
  simp only [bobLedgerLiability, certified_withholding_detected, ↓reduceIte]

/-- This audit also detects ordinary explicit withholding, because the candidate
source implementation uses silence for that branch. -/
theorem explicit_withholding_detected (bit : Bool) :
    bobLedgerViolation (quietGuessIncluded bit false) = true := by
  rw [bobLedgerViolation, canonical_withholding_ledger]
  rfl

theorem silence_clear (bit : Bool) :
    bobLedgerViolation ((quietBob bit).respond nativeApp bob nativeSilent) = false := by
  change ledgerViolation bob bobPacketPermitted (quietBob bit).network.ledger = false
  rw [quiet_bob_network]
  rfl

theorem expiry_preserves_clear (execution next : nativeApp.Execution)
    (event : nativeGraph.EventId) (clear : bobLedgerViolation execution = false)
    (reached : next ∈
      (execution.environmentStep nativeApp (.application (.expire event))).support) :
    bobLedgerViolation next = false :=
  (nativeApp.ledgerViolation_application bob bobPacketPermitted
    execution next (.expire event) reached).trans clear

def plainOpening : WitnessedSubmission nativeGraph :=
  ⟨⟨.opening bobPublication bobHandle ⟨.bool, true⟩, none⟩, .none⟩

def plainOpeningRespond (bit : Bool) : nativeApp.Execution :=
  (quietBob bit).respond nativeApp bob ⟨some (.submit plainOpening)⟩

def plainOpeningIncluded (bit : Bool) : nativeApp.Execution :=
  let before := plainOpeningRespond bit
  { before.includePending nativeApp (bob, 0) with
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .include (bob, 0)⟩] }

theorem plain_opening_available (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) :
    (⟨some (.submit plainOpening)⟩ : nativeApp.Action) ∈ nativeMenu.actions bob past view := by
  change (⟨some (.submit plainOpening)⟩ : nativeApp.Action) ∈
    (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions bob past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change plainOpening ∈ _
  rw [MessageBounds.submissions_mem]
  exact ⟨⟨⟨trivial, by decide⟩, trivial⟩, trivial⟩

theorem plain_opening_included (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob) (plainOpeningRespond bit) =
        PMF.pure (plainOpeningIncluded bit) := by
  have selected : nativeRuntime.reactiveLatest nativeLeaks bobPublication bob
      ((plainOpeningRespond bit).observeEnvironment nativeApp) = .include (bob, 0) := by
    simpa only [plainOpeningRespond, quiet_bob_network, MessageNetwork.empty] using
      nativeRuntime.reactiveLatest_after_submit nativeLeaks bob bobPublication
        (quietBob bit) (quiet_bob_serials bit) plainOpening rfl
  rw [nativeRuntime.interaction_includeLatest_environment, selected]
  change (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  rfl

theorem plain_opening_accepted (bit : Bool) :
    (plainOpeningIncluded bit).application = (quietGuessIncluded bit true).application ∧
      (plainOpeningIncluded bit).receipts = [((bob, 0), true)] := by
  obtain ⟨next, accepted, _, applicationEq, _⟩ := quiet_guess_application bit true
  have law := resolution_submission_inclusion (fun _ => nativeAlicePolicy)
    (quietBob bit) bob bobPublication plainOpening next (quiet_bob_serials bit)
    rfl rfl (by simpa only [plainOpening, quiet_bob_network,
      MessageNetwork.empty, ↓reduceIte] using accepted)
  change (nativeRuntime.interactionStep nativeLeaks (fun _ => nativeAlicePolicy) nativeNetwork
    (.includeLatest bobPublication bob) (plainOpeningRespond bit)).map
    (fun result => (result.application, result.receipts)) = _ at law
  rw [plain_opening_included, PMF.pure_map] at law
  have pair := (PMF.mem_support_pure_iff _ _).mp (law ▸ (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact ⟨(congrArg Prod.fst pair).trans applicationEq.symm, congrArg Prod.snd pair⟩

theorem plain_opening_ledger (bit : Bool) :
    (plainOpeningIncluded bit).network.ledger =
      [⟨(bob, 0), ⟨.opening bobPublication bobHandle ⟨.bool, true⟩, none,
        some ⟨bobPublication⟩⟩⟩] := by
  change ((plainOpeningRespond bit).includePending nativeApp (bob, 0)).network.ledger = _
  rw [nativeApp.includePending_network]
  change (((quietBob bit).network.submit bob
    (⟨.opening bobPublication bobHandle ⟨.bool, true⟩, none,
      (quietBob bit).application.publicView.tokenFor
        (.opening bobPublication bobHandle ⟨.bool, true⟩)⟩ : WitnessedPacket nativeGraph)).2
      |>.includePending (bob, 0)).2.ledger = _
  rw [quiet_bob_network, quiet_bob_token bit (.opening bobPublication bobHandle ⟨.bool, true⟩) rfl]
  simp [MessageNetwork.includePending, MessageNetwork.lookup, MessageNetwork.submit,
    MessageNetwork.empty]

theorem plain_opening_detected (bit : Bool) :
    bobLedgerViolation (plainOpeningIncluded bit) = true := by
  rw [bobLedgerViolation, plain_opening_ledger]
  rfl

theorem canonical_opening_ledger (bit : Bool) :
    (quietGuessIncluded bit true).network.ledger =
      [⟨(bob, 0), ⟨.opening bobPublication bobHandle ⟨.bool, true⟩,
        some ⟨bobHandle, ⟨.bool, true⟩⟩, some ⟨bobPublication⟩⟩⟩] := by
  have emitted : (⟨⟨.opening bobPublication bobHandle ⟨.bool, true⟩, none⟩,
      .owned ⟨bobHandle, ⟨.bool, true⟩⟩⟩ : WitnessedSubmission nativeGraph).emit
      (quietBob bit).application bob ((quietBob bit).network.known bob) =
        ⟨.opening bobPublication bobHandle ⟨.bool, true⟩,
          some ⟨bobHandle, ⟨.bool, true⟩⟩, some ⟨bobPublication⟩⟩ := by
    change WitnessedPacket.mk _ _ ((quietBob bit).application.publicView.tokenFor _) = _
    rw [quiet_bob_token bit (.opening bobPublication bobHandle ⟨.bool, true⟩) rfl]
    exact congrArg (fun evidence => WitnessedPacket.mk
      (.opening bobPublication bobHandle ⟨.bool, true⟩) evidence (some ⟨bobPublication⟩))
      (WitnessedSubmission.emit_owned
        (⟨.opening bobPublication bobHandle ⟨.bool, true⟩, none⟩ : Submission nativeGraph)
        (quietBob bit).application bob ((quietBob bit).network.known bob)
        ⟨bobHandle, ⟨.bool, true⟩⟩ rfl (quiet_bob_fixed bit).bob_candidate)
  change ((quietGuessRespond bit true).includePending nativeApp (bob, 0)).network.ledger = _
  rw [nativeApp.includePending_network]
  change (((quietBob bit).network.submit bob
    ((⟨⟨.opening bobPublication bobHandle ⟨.bool, true⟩, none⟩,
      .owned ⟨bobHandle, ⟨.bool, true⟩⟩⟩ : WitnessedSubmission nativeGraph).emit
      (quietBob bit).application bob ((quietBob bit).network.known bob))).2.includePending
        (bob, 0)).2.ledger = _
  rw [emitted, quiet_bob_network]
  simp [MessageNetwork.includePending, MessageNetwork.lookup, MessageNetwork.submit,
    MessageNetwork.empty]

theorem canonical_opening_clear (bit : Bool) :
    bobLedgerViolation (quietGuessIncluded bit true) = false := by
  rw [bobLedgerViolation, canonical_opening_ledger]
  simp [ledgerViolation, bobPacketPermitted]

/-- The new evidence-based liability is persistent under all future raw policies.
Applying this score as a monetary utility loss is a separate backend assumption. -/
theorem certified_withholding_liability_persists (bit : Bool)
    (players : Player → nativeApp.Policy) (scheduler : nativeApp.Scheduler)
    (count : Nat) (next : nativeApp.Execution)
    (reached : next ∈ (nativeApp.runRounds scheduler players count
      (certifiedWithholdIncluded bit)).support) :
    bobLedgerLiability next = 1 := by
  have detected := nativeApp.ledgerViolation_continuation bob bobPacketPermitted
    players scheduler count (certifiedWithholdIncluded bit) next
    (certified_withholding_detected bit) reached
  simp only [bobLedgerLiability, bobLedgerViolation, detected, ↓reduceIte]

end Vegas.Examples.MonitoredGuessing.Conformance
