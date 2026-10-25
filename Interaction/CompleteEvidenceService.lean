/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ChallengeWindow

/-! # Complete observation and immediate delivery of authentic evidence -/

noncomputable section

namespace Interaction.EvidenceReportService

open GameTheory.Math.Probability

/-- Every observed item is reported and included immediately. The kernels read
only their actual input lists and introduce no synthetic evidence. -/
def complete (Evidence : Type*) : EvidenceReportService Evidence where
  window := ⟨0, 0, 0, by omega⟩
  observations := PMF.pure
  reports := fun seen => PMF.pure (seen.map fun evidence => ⟨evidence, 0, 0⟩)
  observations_authentic := by
    intro actual seen supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact List.Subset.refl _
  reports_authentic := by
    intro seen delivered supported report member
    cases (PMF.mem_support_pure_iff _ _).mp supported
    obtain ⟨evidence, present, rfl⟩ := List.mem_map.mp member
    exact present
  reports_timelySubmitted := by
    intro seen delivered supported report member
    cases (PMF.mem_support_pure_iff _ _).mp supported
    obtain ⟨evidence, _, rfl⟩ := List.mem_map.mp member
    exact ⟨le_rfl, le_rfl⟩

variable {Evidence : Type*}

@[simp]
theorem complete_deliveredEvidence (actual : List Evidence) :
    EvidenceReport.deliveredEvidence 0
      (actual.map fun evidence => (⟨evidence, 0, 0⟩ : EvidenceReport Evidence)) = actual := by
  induction actual with
  | nil => rfl
  | cons first rest ih =>
    simpa [EvidenceReport.deliveredEvidence] using congrArg (first :: ·) ih

@[simp]
theorem complete_sample (actual : List Evidence) :
    (complete Evidence).sample actual = PMF.pure actual := by
  classical
  simp only [sample, complete, PMF.pure_bind, PMF.pure_map, complete_deliveredEvidence]

theorem complete_observation_mass (actual : List Evidence) (evidence : Evidence)
    (member : evidence ∈ actual) :
    (((complete Evidence).observations actual).toOuterMeasure
      {seen | evidence ∈ seen}).toReal = 1 := by
  classical
  simp [complete, PMF.toOuterMeasure_pure_apply, member]

theorem complete_delivery_mass (seen : List Evidence) (evidence : Evidence)
    (member : evidence ∈ seen) :
    (((complete Evidence).reports seen).toOuterMeasure {delivered |
      evidence ∈ EvidenceReport.deliveredEvidence
        ((complete Evidence).window.reportCutoff + (complete Evidence).window.inclusionBound)
        delivered}).toReal = 1 := by
  classical
  simp [complete, PMF.toOuterMeasure_pure_apply, complete_deliveredEvidence, member]

end Interaction.EvidenceReportService
