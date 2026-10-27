/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ChallengeWindow
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Authentic evidence service with imperfect capture and delivery

Each stage retains its whole input list or loses it. Capture and delivery are
separate kernels; within a stage the fates of distinct items are correlated.
These kernels specify an evidence backend, not a ledger-only implementation.
-/

noncomputable section

namespace Interaction.EvidenceReportService

open GameTheory.Math.Probability

variable {Evidence : Type*}

private def erase {α : Type*} (rate : Set.Icc (0 : ℝ) 1) (values : List α) :
    PMF (List α) :=
  mix rate.val rate.property.1 rate.property.2 (PMF.pure values) (PMF.pure [])

private theorem erase_support {α : Type*} (rate : Set.Icc (0 : ℝ) 1)
    (values result : List α) (supported : result ∈ (erase rate values).support) :
    result = values ∨ result = [] := by
  have member := support_mix_subset rate.val rate.property.1 rate.property.2
    (PMF.pure values) (PMF.pure []) supported
  simpa only [PMF.support_pure, Set.mem_union, Set.mem_singleton_iff] using member

private theorem erase_mass {α : Type*} (rate : Set.Icc (0 : ℝ) 1)
    (values : List α) (event : Set (List α)) (present : values ∈ event)
    (absent : [] ∉ event) :
    ((erase rate values).toOuterMeasure event).toReal = rate.val := by
  classical
  rw [← expect_indicator]
  change expect (erase rate values) (event.indicator (fun _ => (1 : ℝ))) = rate.val
  rw [erase, expect_mix rate.val rate.property.1 rate.property.2 _ _ _
    (payoffIntegrable_indicator event (payoffIntegrable_constant _ 1))
    (payoffIntegrable_indicator event (payoffIntegrable_constant _ 1))]
  simp [expect_pure, Set.indicator_of_mem present, Set.indicator_of_notMem absent]

/-- Retain evidence with the stated capture rate and retain timely reports with
the stated conditional delivery rate. Reports take one time unit to arrive. -/
def thinned (capture delivery : Set.Icc (0 : ℝ) 1) : EvidenceReportService Evidence where
  window := ⟨0, 1, 1, by omega⟩
  observations := erase capture
  reports := fun seen => erase delivery (seen.map fun evidence => ⟨evidence, 0, 1⟩)
  observations_authentic := by
    intro actual seen supported
    rcases erase_support capture actual seen supported with rfl | rfl
    · exact List.Subset.refl _
    · exact List.nil_subset _
  reports_authentic := by
    intro seen delivered supported report member
    rcases erase_support delivery _ delivered supported with rfl | rfl
    · obtain ⟨evidence, present, rfl⟩ := List.mem_map.mp member
      exact present
    · simp at member
  reports_timelySubmitted := by
    intro seen delivered supported report member
    rcases erase_support delivery _ delivered supported with rfl | rfl
    · obtain ⟨evidence, _, rfl⟩ := List.mem_map.mp member
      exact ⟨le_rfl, Nat.zero_le 1⟩
    · simp at member

private theorem delivered_map (seen : List Evidence) :
    EvidenceReport.deliveredEvidence 1
      (seen.map fun evidence => (⟨evidence, 0, 1⟩ : EvidenceReport Evidence)) = seen := by
  induction seen with
  | nil => rfl
  | cons first rest ih =>
      simpa [EvidenceReport.deliveredEvidence] using congrArg (first :: ·) ih

theorem thinned_observation_mass (capture delivery : Set.Icc (0 : ℝ) 1)
    (actual : List Evidence) (evidence : Evidence) (member : evidence ∈ actual) :
    (((thinned capture delivery).observations actual).toOuterMeasure
      {seen | evidence ∈ seen}).toReal = capture.val :=
  erase_mass capture actual _ member (by simp)

theorem thinned_delivery_mass (capture delivery : Set.Icc (0 : ℝ) 1)
    (seen : List Evidence) (evidence : Evidence) (member : evidence ∈ seen) :
    (((thinned capture delivery).reports seen).toOuterMeasure {reports |
      evidence ∈ EvidenceReport.deliveredEvidence
        ((thinned (Evidence := Evidence) capture delivery).window.reportCutoff +
          (thinned (Evidence := Evidence) capture delivery).window.inclusionBound)
        reports}).toReal = delivery.val := by
  apply erase_mass delivery _ _
  · change evidence ∈ EvidenceReport.deliveredEvidence 1 _
    simpa only [delivered_map] using member
  · simp [thinned, EvidenceReport.deliveredEvidence]

/-- The probability of collecting a particular actual item is bounded below by
the product of capture and conditional delivery rates. -/
theorem thinned_collection (capture delivery : Set.Icc (0 : ℝ) 1)
    (actual : List Evidence) (evidence : Evidence) (member : evidence ∈ actual) :
    capture.val * delivery.val ≤
      (((thinned capture delivery).sample actual).toOuterMeasure
        {collected | evidence ∈ collected}).toReal := by
  apply sample_coverage _ actual evidence capture.val delivery.val delivery.property.1
  · exact (thinned_observation_mass capture delivery actual evidence member).symm.le
  · intro seen _ present
    exact (thinned_delivery_mass capture delivery seen evidence present).symm.le

/-- For an actual item, the catch probability is exactly the product. Thus
strictly subunit capture or delivery is a genuinely imperfect audit. -/
theorem thinned_collection_mass (capture delivery : Set.Icc (0 : ℝ) 1)
    (actual : List Evidence) (evidence : Evidence) (member : evidence ∈ actual) :
    (((thinned capture delivery).sample actual).toOuterMeasure
      {collected | evidence ∈ collected}).toReal = capture.val * delivery.val := by
  classical
  let service := thinned (Evidence := Evidence) capture delivery
  let event : Set (List Evidence) := {collected | evidence ∈ collected}
  let delivered := fun seen => (service.reports seen).map
    (EvidenceReport.deliveredEvidence service.window.settlementTime)
  change ((service.sample actual).toOuterMeasure event).toReal = _
  rw [sample, toReal_toOuterMeasure_bind]
  change expect (erase capture actual) (fun seen =>
    ((delivered seen).toOuterMeasure event).toReal) = _
  rw [erase, expect_mix _ _ _ _ _ _
    (payoffIntegrable_toReal_toOuterMeasure _ delivered event)
    (payoffIntegrable_toReal_toOuterMeasure _ delivered event)]
  simp only [expect_pure]
  have present : ((delivered actual).toOuterMeasure event).toReal = delivery.val := by
    rw [show delivered actual = (service.reports actual).map
      (EvidenceReport.deliveredEvidence 1) from rfl, PMF.toOuterMeasure_map_apply]
    exact thinned_delivery_mass capture delivery actual evidence member
  have absent : ((delivered []).toOuterMeasure event).toReal = 0 := by
    simp [delivered, service, event, thinned, erase, mix_self,
      EvidenceReport.deliveredEvidence, PMF.toOuterMeasure_pure_apply]
  rw [present, absent]
  ring

end Interaction.EvidenceReportService
