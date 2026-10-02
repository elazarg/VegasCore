/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeAuditFacts
import Interaction.ChallengeWindow

/-! # Actual report delivery and terminal deposit collection

The watcher has already sampled its private observation in the runtime. This
backend submits exactly that evidence, and includes all reports with a fixed
conditional probability `rate`. The complementary outcome collects nothing.
The rate is a backend assumption specified conditional on the observed record,
and includes censorship or delay of the watcher's reports.
Only authentic evidence delivered by settlement is inspected, and punishment
requires a completed final record. Prefix comparison utilities are separate.

The challenge clock measures elapsed time after gameplay has completed and
the final public ledger is available to the reporter. Its time zero therefore
includes the retained private observation and final ledger supplied below;
the cutoff and report timestamps use this later epoch, not the gameplay clock.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

abbrev NativeEvidence := Message Player (WitnessedPacket nativeGraph)

def nativeEvidenceReport (window : ChallengeWindow) (message : NativeEvidence) :
    EvidenceReport NativeEvidence :=
  ⟨message, window.reportCutoff, window.reportCutoff + window.inclusionBound⟩

def nativeReportService (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) : EvidenceReportService NativeEvidence where
  window := window
  observations := PMF.pure
  reports observed := mix rate nonnegative bounded
    (PMF.pure (observed.map (nativeEvidenceReport window))) (PMF.pure [])
  observations_authentic actual observed supported := by
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact List.Subset.refl _
  reports_authentic observed delivered supported report present := by
    rcases support_mix_subset rate nonnegative bounded _ _ supported with included | omitted
    · cases (PMF.mem_support_pure_iff _ _).mp included
      obtain ⟨message, member, rfl⟩ := List.mem_map.mp present
      exact member
    · cases (PMF.mem_support_pure_iff _ _).mp omitted
      cases present
  reports_timelySubmitted observed delivered supported report present := by
    rcases support_mix_subset rate nonnegative bounded _ _ supported with included | omitted
    · cases (PMF.mem_support_pure_iff _ _).mp included
      obtain ⟨message, _, rfl⟩ := List.mem_map.mp present
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
    · cases (PMF.mem_support_pure_iff _ _).mp omitted
      cases present

theorem native_reports_delivered (window : ChallengeWindow) (observed : List NativeEvidence) :
    EvidenceReport.deliveredEvidence window.settlementTime
      (observed.map (nativeEvidenceReport window)) = observed := by
  induction observed with
  | nil => rfl
  | cons message rest ih =>
      simp only [EvidenceReport.deliveredEvidence, List.map_cons, List.filter_cons,
        nativeEvidenceReport, decide_eq_true window.settlement_waits, ↓reduceIte]
      simpa only [EvidenceReport.deliveredEvidence] using congrArg (List.cons message) ih

theorem native_report_sample (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (observed : List NativeEvidence) :
    (nativeReportService window rate nonnegative bounded).sample observed =
      mix rate nonnegative bounded (PMF.pure observed) (PMF.pure []) := by
  simp only [EvidenceReportService.sample, nativeReportService, PMF.pure_bind,
    mix_map, PMF.pure_map, native_reports_delivered]
  rfl

def nativeCollectedResult (deposit : ℝ) (execution : nativeApp.Execution)
    (collected : List NativeEvidence) : Results × (Player → ℝ) :=
  (nativeResults execution.application.config, fun who =>
    utility (nativeResults execution.application.config) who -
      if who = alice ∧ collected.any (nativeAuditVerdict execution) then deposit else 0)

open Classical in
/-- The physical settlement law includes genuine report-delivery failure.
Unresolved records do not authorize deposit collection. -/
def nativeCollectionLaw (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ)
    (execution : nativeApp.Execution) : PMF (Results × (Player → ℝ)) :=
  if execution.application.config.cut.Terminal then
    ((nativeReportService window rate nonnegative bounded).sample
      (nativeAuditPackets execution)).map (nativeCollectedResult deposit execution)
  else PMF.pure (nativeCollectedResult deposit execution [])

theorem nativeCollectionLaw_complete (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ)
    (execution : nativeApp.Execution) (complete : execution.application.config.cut.Terminal) :
    nativeCollectionLaw window rate nonnegative bounded deposit execution =
      mix rate nonnegative bounded
        (PMF.pure (nativeCollectedResult deposit execution (nativeAuditPackets execution)))
        (PMF.pure (nativeCollectedResult deposit execution [])) := by
  rw [nativeCollectionLaw, ite_eq_left complete, native_report_sample, mix_map, PMF.pure_map,
    PMF.pure_map]

theorem nativeCollectionLaw_expected (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ)
    (execution : nativeApp.Execution) (facts : NativeReceipts execution)
    (unique : execution.network.UniqueIds) (once : execution.network.PublishedOnce)
    (complete : execution.application.config.cut.Terminal) (who : Player) :
    expect (nativeCollectionLaw window rate nonnegative bounded deposit execution)
      (fun result => result.2 who) =
        nativeComparisonExecutionUtility (rate * deposit) who execution := by
  rw [nativeCollectionLaw_complete window rate nonnegative bounded deposit execution complete,
    expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
    expect_pure, expect_pure]
  simp only [nativeCollectedResult, nativeAuditVerdict_eq_liability execution facts unique once
    complete, List.any_nil, Bool.false_eq_true, and_false, ↓reduceIte,
    nativeComparisonExecutionUtility]
  split_ifs <;> ring

theorem nativeCollectionLaw_clean (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ)
    (execution : nativeApp.Execution) (facts : NativeReceipts execution)
    (unique : execution.network.UniqueIds) (once : execution.network.PublishedOnce)
    (complete : execution.application.config.cut.Terminal)
    (clean : aliceLiability execution = false) :
    nativeCollectionLaw window rate nonnegative bounded deposit execution =
      PMF.pure (nativeResults execution.application.config,
        fun who => utility (nativeResults execution.application.config) who) := by
  rw [nativeCollectionLaw_complete window rate nonnegative bounded deposit execution complete]
  simp only [nativeCollectedResult, nativeAuditVerdict_eq_liability execution facts unique once
    complete, clean, Bool.false_eq_true, and_false, ↓reduceIte, List.any_nil, sub_zero, mix_self]

end Vegas.Examples.MonitoredGuessing
