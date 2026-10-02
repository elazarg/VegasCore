/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeSettlement
import Vegas.Examples.MonitoredGuessing.EnforcementPayoffs

/-! # Physical collection for declared return tables

Alice's audit checks rejected authentic evidence against the completed record.
Bob's separate policy conformance audit checks immutable packet format in the
public ledger. This source-specific format predicate also detects accepted
extra disclosures; it does not claim rejection by the application handler.
Both audits wait for the completed final record and actual report inclusion.
The physical deposit compensates for the explicit conditional delivery rate.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Enforcement

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

open Classical in
def bobFormatVerdict (execution : nativeApp.Execution) (message : NativeEvidence) : Bool :=
  decide (message ∈ execution.network.ledger) &&
    decide (message.sender = bob) && !Conformance.bobPacketPermitted message.payload

theorem bobFormatVerdict_eq_violation (execution : nativeApp.Execution) :
    (nativeAuditPackets execution).any (bobFormatVerdict execution) =
      Conformance.bobLedgerViolation execution := by
  classical
  apply Bool.eq_iff_iff.mpr
  change ((nativeAuditPackets execution).any (bobFormatVerdict execution) = true) ↔
    ledgerViolation bob Conformance.bobPacketPermitted execution.network.ledger = true
  constructor
  · intro detected
    obtain ⟨message, _, verdict⟩ := List.any_eq_true.mp detected
    have classified : message ∈ execution.network.ledger ∧ message.sender = bob ∧
        Conformance.bobPacketPermitted message.payload = false := by
      simpa only [bobFormatVerdict, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true_eq_eq_false, and_assoc] using verdict
    exact (ledgerViolation_iff bob Conformance.bobPacketPermitted
      execution.network.ledger).mpr ⟨message, classified.1, classified.2⟩
  · intro detected
    obtain ⟨message, published, sender, rejected⟩ :=
      (ledgerViolation_iff bob Conformance.bobPacketPermitted
        execution.network.ledger).mp detected
    apply List.any_eq_true.mpr
    refine ⟨message, List.mem_append_left _ published, ?_⟩
    simp only [bobFormatVerdict, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true_eq_eq_false]
    exact ⟨⟨published, sender⟩, rejected⟩

def tableVerdict (execution : nativeApp.Execution) (who : Player)
    (message : NativeEvidence) : Bool :=
  if who = alice then nativeAuditVerdict execution message
  else if who = bob then bobFormatVerdict execution message else false

theorem tableVerdict_score (execution : nativeApp.Execution) (facts : NativeReceipts execution)
    (unique : execution.network.UniqueIds) (once : execution.network.PublishedOnce)
    (complete : execution.application.config.cut.Terminal) (who : Player) :
    (if (nativeAuditPackets execution).any (tableVerdict execution who) then (1 : ℝ) else 0) =
      liability execution who := by
  unfold tableVerdict
  by_cases aliceOwner : who = alice
  · simp only [liability, ite_eq_left aliceOwner]
    rw [nativeAuditVerdict_eq_liability execution facts unique once complete]
  · by_cases bobOwner : who = bob
    · simp only [liability, ite_eq_right aliceOwner, ite_eq_left bobOwner]
      rw [bobFormatVerdict_eq_violation]
      rfl
    · have absent : (nativeAuditPackets execution).any (fun _ => false) = false :=
        List.any_eq_false.mpr (fun _ _ => Bool.false_ne_true)
      simp only [liability, ite_eq_right aliceOwner, ite_eq_right bobOwner, absent,
        Bool.false_eq_true, ↓reduceIte]

/-- Physical escrow is larger when conditional report inclusion is less likely. -/
def physicalDeposit (table : PayoffTable) (rate : ℝ) (who : Player) : ℝ :=
  (charge table who : ℝ) / rate

theorem physicalDeposit_nonnegative (table : PayoffTable) (rate : ℝ)
    (positive : 0 < rate) (who : Player) : 0 ≤ physicalDeposit table rate who :=
  div_nonneg (by exact_mod_cast charge_nonnegative table who) positive.le

def collectedTableResult (table : PayoffTable) (rate : ℝ) (execution : nativeApp.Execution)
    (collected : List NativeEvidence) : Results × (Player → ℝ) :=
  (nativeResults execution.application.config, fun who =>
    (table (nativeResults execution.application.config) who : ℝ) -
      physicalDeposit table rate who *
        (if collected.any (tableVerdict execution who) then 1 else 0))

open Classical in
def collectionLaw (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1)
    (execution : nativeApp.Execution) : PMF (Results × (Player → ℝ)) :=
  if execution.application.config.cut.Terminal then
    ((nativeReportService window rate nonnegative bounded).sample
      (nativeAuditPackets execution)).map (collectedTableResult table rate execution)
  else PMF.pure (collectedTableResult table rate execution [])

theorem collectionLaw_complete (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (execution : nativeApp.Execution)
    (complete : execution.application.config.cut.Terminal) :
    collectionLaw table window rate nonnegative bounded execution =
      mix rate nonnegative bounded
        (PMF.pure (collectedTableResult table rate execution (nativeAuditPackets execution)))
        (PMF.pure (collectedTableResult table rate execution [])) := by
  rw [collectionLaw, ite_eq_left complete, native_report_sample, mix_map, PMF.pure_map,
    PMF.pure_map]

theorem collectionLaw_expected (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (positive : 0 < rate) (bounded : rate ≤ 1) (execution : nativeApp.Execution)
    (facts : NativeReceipts execution) (unique : execution.network.UniqueIds)
    (once : execution.network.PublishedOnce) (complete : execution.application.config.cut.Terminal)
    (who : Player) :
    expect (collectionLaw table window rate positive.le bounded execution)
      (fun result => result.2 who) = comparisonExecutionUtility table execution who := by
  rw [collectionLaw_complete table window rate positive.le bounded execution complete,
    expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
    expect_pure, expect_pure]
  simp only [collectedTableResult, tableVerdict_score execution facts unique once complete,
    List.any_nil, Bool.false_eq_true, ↓reduceIte, mul_zero, sub_zero,
    physicalDeposit, comparisonExecutionUtility]
  field_simp [ne_of_gt positive]
  ring

theorem collectionLaw_clean (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (execution : nativeApp.Execution)
    (facts : NativeReceipts execution) (unique : execution.network.UniqueIds)
    (once : execution.network.PublishedOnce) (complete : execution.application.config.cut.Terminal)
    (aliceClear : aliceLiability execution = false)
    (bobClear : Conformance.bobLedgerViolation execution = false) :
    collectionLaw table window rate nonnegative bounded execution =
      PMF.pure (nativeResults execution.application.config,
        fun who => (table (nativeResults execution.application.config) who : ℝ)) := by
  have noCharge (who : Player) :
      (if (nativeAuditPackets execution).any (tableVerdict execution who) then (1 : ℝ) else 0) =
        0 := by
    rw [tableVerdict_score execution facts unique once complete, liability]
    simp only [aliceClear, Conformance.bobLedgerLiability, bobClear,
      Bool.false_eq_true, ↓reduceIte, ite_self]
  rw [collectionLaw_complete table window rate nonnegative bounded execution complete]
  simp only [collectedTableResult, noCharge, List.any_nil, Bool.false_eq_true,
    ↓reduceIte, mul_zero, sub_zero, mix_self]

/-- Equality of the comparison payoff to the declared return eliminates actual
collection losses too, including when the table's expected charge is zero. -/
theorem collectionLaw_no_loss (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (execution : nativeApp.Execution)
    (facts : NativeReceipts execution) (unique : execution.network.UniqueIds)
    (once : execution.network.PublishedOnce) (complete : execution.application.config.cut.Terminal)
    (unpenalized : ∀ who, comparisonExecutionUtility table execution who =
      (table (nativeResults execution.application.config) who : ℝ)) :
    collectionLaw table window rate nonnegative bounded execution =
      PMF.pure (nativeResults execution.application.config,
        fun who => (table (nativeResults execution.application.config) who : ℝ)) := by
  have noCharge (who : Player) : (charge table who : ℝ) * liability execution who = 0 := by
    have equal := unpenalized who
    unfold comparisonExecutionUtility at equal
    linarith
  have full : collectedTableResult table rate execution (nativeAuditPackets execution) =
      collectedTableResult table rate execution [] := by
    unfold collectedTableResult
    refine Prod.ext rfl ?_
    funext who
    change _ - physicalDeposit table rate who *
      (if (nativeAuditPackets execution).any (tableVerdict execution who) then 1 else 0) =
        _ - physicalDeposit table rate who * (if [].any (tableVerdict execution who) then 1 else 0)
    rw [tableVerdict_score execution facts unique once complete]
    simp only [physicalDeposit, div_mul_eq_mul_div, noCharge, zero_div, List.any_nil,
      Bool.false_eq_true, ↓reduceIte, mul_zero, sub_zero]
  rw [collectionLaw_complete table window rate nonnegative bounded execution complete, full,
    mix_self]
  simp only [collectedTableResult, List.any_nil, Bool.false_eq_true, ↓reduceIte, mul_zero, sub_zero]

def settledStateUtility (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (state : nativeApp.ProtocolState)
    (who : Player) : ℝ :=
  state.elim 0 fun control =>
    expect (collectionLaw table window rate nonnegative bounded control.execution)
      (fun result => result.2 who)

def collectedObservation (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (state : nativeApp.ProtocolState) :
    PMF (Bool × Results × (Player → ℝ)) :=
  state.elim (PMF.pure (false, ⟨.failure, .failure⟩, fun _ => 0)) fun control =>
    (collectionLaw table window rate nonnegative bounded control.execution).map
      (fun result => (observedAliceBit (control.execution.observe nativeApp alice), result))

theorem settled_terminal_utility_eq (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (positive : 0 < rate) (bounded : rate ≤ 1) (who : Player) (history : nativeArena.History)
    (terminal : nativeArena.terminal history.state) :
    settledStateUtility table window rate positive.le bounded history.state who =
      comparisonStateUtility table history.state who := by
  cases state : history.state with
  | none => rfl
  | some control =>
      have trace : nativeArena.Trace (some control) := state ▸ history.trace
      have finished : nativeArena.terminal (some control) := state ▸ terminal
      have raw := nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace
      exact collectionLaw_expected table window rate positive bounded control.execution
        (nativeReceipts_history control raw)
        (nativeApp.uniqueIds_history nativeScheduler nativeInitialLaw nativeHorizon control raw)
        (nativeApp.publishedOnce_history nativeScheduler nativeInitialLaw nativeHorizon raw)
        (native_terminal_control_complete control trace finished) who

theorem settled_equilibrium_iff (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (positive : 0 < rate) (bounded : rate ≤ 1) (assessment : nativeModel.BehavioralAssessment) :
    assessment.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        assessment.truncatedContinuationContext site
          (fun history => comparisonStateUtility table history.state who)
          (2 * nativeHorizon + 1)) ↔
      assessment.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        assessment.truncatedContinuationContext site
          (fun history => settledStateUtility table window rate positive.le bounded history.state
            who) (2 * nativeHorizon + 1)) := by
  let horizon := nativeMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler
  exact assessment.isSequentialEquilibriumFor_iff_of_bounded_terminal_payoff_eq
    nativeAntichain horizon.wellFoundedHistories horizon _ _ (fun who history terminal =>
      (settled_terminal_utility_eq table window rate positive bounded who history terminal).symm)

end Vegas.Examples.MonitoredGuessing.Enforcement
