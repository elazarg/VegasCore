module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ChallengeWindow

@[expose] public section

/-! # Timely submission with inclusion after settlement -/

noncomputable section

namespace Interaction.EvidenceReportService

variable {Evidence : Type*}

/-- Every item is captured and submitted immediately. Each report is included
one tick after the settlement time. -/
def afterSettlement (window : ChallengeWindow) : EvidenceReportService Evidence where
  window := window
  observations := PMF.pure
  reports := fun seen => PMF.pure (seen.map fun item => ⟨item, 0, window.settlementTime + 1⟩)
  observations_authentic := by simp
  reports_authentic := by
    intro seen reports supported report member
    obtain rfl : reports = _ := by simpa using supported
    obtain ⟨_, observed, rfl⟩ := List.mem_map.mp member
    exact observed
  reports_timelySubmitted := by
    intro seen reports supported report member
    obtain rfl : reports = _ := by simpa using supported
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem afterSettlement_sample (window : ChallengeWindow) (actual : List Evidence) :
    (afterSettlement window).sample actual = PMF.pure [] := by
  simp [sample, afterSettlement, PMF.pure_map, EvidenceReport.deliveredEvidence, List.filter_map,
    Function.comp_def]

/-- Zero is the greatest uniform lower bound for collection of any event
requiring evidence, even with perfect capture and immediate submission of
every item in order. The time of inclusion is unrestricted. -/
theorem uniform_collection_bound_iff (window : ChallengeWindow) (actual : List Evidence)
    (event : Set (List Evidence)) (needsEvidence : [] ∉ event) (bound : ℝ) :
    (∀ service : EvidenceReportService Evidence, service.window = window →
      service.observations actual = PMF.pure actual →
      (∀ reports ∈ (service.reports actual).support,
        reports.map EvidenceReport.evidence = actual ∧ ∀ r ∈ reports, r.submittedAt = 0) →
      bound ≤ ((service.sample actual).toOuterMeasure event).toReal) ↔ bound ≤ 0 := by
  classical
  constructor
  · intro uniform
    have lower := uniform (afterSettlement window) rfl rfl (by
      intro reports supported
      obtain rfl : reports = _ := by simpa [afterSettlement] using supported
      constructor
      · simp [List.map_map, Function.comp_def]
      · intro r member
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
        rfl)
    simpa [afterSettlement_sample, PMF.toOuterMeasure_pure_apply, needsEvidence] using lower
  · intro nonpos service _ _ _
    exact nonpos.trans ENNReal.toReal_nonneg

end Interaction.EvidenceReportService
