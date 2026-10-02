/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Expectation
import GameTheory.Math.Probability.Bounds

/-! # Evidence delivery before settlement

Monitoring and report delivery are separate service kernels. Reports may be
lost or arrive after settlement. Only reports actually delivered before
settlement contribute evidence. A conditional delivery guarantee during the
challenge window combines with observation coverage without an independence
assumption. These are backend hypotheses, not consequences of owner service.
-/

noncomputable section

namespace Interaction

open GameTheory.Math.Probability

/-- A report carries observed evidence and its submission and inclusion times. -/
structure EvidenceReport (Evidence : Type*) where
  evidence : Evidence
  submittedAt : Nat
  includedAt : Nat

namespace EvidenceReport

variable {Evidence : Type*}

def deliveredEvidence (deadline : Nat) (reports : List (EvidenceReport Evidence)) :
    List Evidence :=
  (reports.filter fun report => report.includedAt ≤ deadline).map EvidenceReport.evidence

theorem mem_deliveredEvidence (deadline : Nat) (reports : List (EvidenceReport Evidence))
    (evidence : Evidence) :
    evidence ∈ deliveredEvidence deadline reports ↔
      ∃ report ∈ reports, report.evidence = evidence ∧ report.includedAt ≤ deadline := by
  simp only [deliveredEvidence, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨report, ⟨present, timely⟩, same⟩
    exact ⟨report, present, same, timely⟩
  · rintro ⟨report, present, same, timely⟩
    exact ⟨report, ⟨present, timely⟩, same⟩

theorem deliveredEvidence_mono {first last : Nat} (ordered : first ≤ last)
    (reports : List (EvidenceReport Evidence)) :
    deliveredEvidence first reports ⊆ deliveredEvidence last reports := by
  intro evidence present
  obtain ⟨report, member, same, timely⟩ := (mem_deliveredEvidence ..).mp present
  exact (mem_deliveredEvidence ..).mpr ⟨report, member, same, timely.trans ordered⟩

end EvidenceReport

/-- The observer stops accepting new evidence at the cutoff; settlement leaves
the specified report-delivery window after that cutoff. -/
structure ChallengeWindow where
  reportCutoff : Nat
  inclusionBound : Nat
  settlementTime : Nat
  settlement_waits : reportCutoff + inclusionBound ≤ settlementTime

/-- An implementable reporting interface uses only evidence actually observed.
The observation law can be partial and correlated. Delivery can depend on the
entire observed record and can omit reports or include them too late. -/
structure EvidenceReportService (Evidence : Type*) where
  window : ChallengeWindow
  observations : List Evidence → PMF (List Evidence)
  reports : List Evidence → PMF (List (EvidenceReport Evidence))
  observations_authentic : ∀ actual observed,
    observed ∈ (observations actual).support → observed ⊆ actual
  reports_authentic : ∀ observed delivered,
    delivered ∈ (reports observed).support →
    ∀ report ∈ delivered, report.evidence ∈ observed
  reports_timelySubmitted : ∀ observed delivered,
    delivered ∈ (reports observed).support → ∀ report ∈ delivered,
    report.submittedAt ≤ window.reportCutoff ∧ report.submittedAt ≤ report.includedAt

namespace EvidenceReportService

variable {Evidence : Type*} (service : EvidenceReportService Evidence)

/-- The audit receives exactly the evidence included by settlement. -/
def sample (actual : List Evidence) : PMF (List Evidence) :=
  (service.observations actual).bind fun observed =>
    (service.reports observed).map
      (EvidenceReport.deliveredEvidence service.window.settlementTime)

theorem sample_authentic (actual collected : List Evidence)
    (supported : collected ∈ (service.sample actual).support) : collected ⊆ actual := by
  obtain ⟨observed, seen, delivered⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨reports, included, rfl⟩ := PMF.support_map .. ▸ delivered
  intro evidence present
  obtain ⟨report, member, same, _⟩ := (EvidenceReport.mem_deliveredEvidence ..).mp present
  rw [← same]
  exact service.observations_authentic actual observed seen
    (service.reports_authentic observed reports included report member)

/-- Coverage bounds actual collection. The delivery bound is conditional on
the complete observation, so no independence of sampling and scheduling is
required. It includes censoring or starvation of reports. -/
theorem sample_coverage (actual : List Evidence) (evidence : Evidence)
    (observationRate deliveryRate : ℝ) (delivery_nonnegative : 0 ≤ deliveryRate)
    (observation_coverage : observationRate ≤
      ((service.observations actual).toOuterMeasure {observed | evidence ∈ observed}).toReal)
    (delivery_coverage : ∀ observed ∈ (service.observations actual).support,
      evidence ∈ observed → deliveryRate ≤
        ((service.reports observed).toOuterMeasure {reports |
          evidence ∈ EvidenceReport.deliveredEvidence
            (service.window.reportCutoff + service.window.inclusionBound) reports}).toReal) :
    observationRate * deliveryRate ≤
      ((service.sample actual).toOuterMeasure {collected | evidence ∈ collected}).toReal := by
  classical
  let event : Set (List Evidence) := {observed | evidence ∈ observed}
  let delivered := fun observed => (service.reports observed).map
    (EvidenceReport.deliveredEvidence service.window.settlementTime)
  have pointwise (observed : List Evidence)
      (supported : observed ∈ (service.observations actual).support) :
      deliveryRate * event.indicator (fun _ => (1 : ℝ)) observed ≤
        ((delivered observed).toOuterMeasure event).toReal := by
    by_cases present : evidence ∈ observed
    · have timely := delivery_coverage observed supported present
      have ordered : {reports | evidence ∈ EvidenceReport.deliveredEvidence
            (service.window.reportCutoff + service.window.inclusionBound) reports} ⊆
          {reports | evidence ∈ EvidenceReport.deliveredEvidence
            service.window.settlementTime reports} :=
        fun reports member => EvidenceReport.deliveredEvidence_mono
          service.window.settlement_waits reports member
      have bound := ENNReal.toReal_mono
        (outerMeasure_ne_top (service.reports observed) _)
        ((service.reports observed).toOuterMeasure_mono (fun reports member => ordered member.1))
      have member : observed ∈ event := present
      simpa only [Set.indicator_of_mem member, mul_one, delivered, event,
        PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using timely.trans bound
    · have absent : observed ∉ event := present
      simp only [Set.indicator_of_notMem absent, mul_zero]
      exact ENNReal.toReal_nonneg
  calc
    observationRate * deliveryRate ≤
        ((service.observations actual).toOuterMeasure event).toReal * deliveryRate :=
      mul_le_mul_of_nonneg_right observation_coverage delivery_nonnegative
    _ = expect (service.observations actual)
        (fun observed => deliveryRate * event.indicator (fun _ => (1 : ℝ)) observed) := by
      rw [expect_const_mul]
      have indicatorLaw : expect (service.observations actual)
          (event.indicator (fun _ => (1 : ℝ))) =
          ((service.observations actual).toOuterMeasure event).toReal := by
        exact expect_indicator _ _
      rw [indicatorLaw]
      ring
    _ ≤ expect (service.observations actual)
        (fun observed => ((delivered observed).toOuterMeasure event).toReal) :=
      expect_mono pointwise
        (payoffIntegrable_const_mul
          (payoffIntegrable_indicator event (payoffIntegrable_constant _ 1)))
        (payoffIntegrable_toReal_toOuterMeasure _ delivered event)
    _ = _ := by
      rw [sample, toReal_toOuterMeasure_bind]

end EvidenceReportService

end Interaction
