/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountCollection
import Interaction.ThinnedEvidenceService

/-! # Conditional coverage from an imperfect evidence backend -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Whole-list capture and delivery losses give the stated coverage at every
actual forbidden item and every supported observed list containing it. -/
theorem thinnedEvidence_coverage (capture delivery : Set.Icc (0 : ℝ) 1) :
    EvidenceCoverage (EvidenceReportService.thinned (Evidence := Evidence graph) capture delivery)
      (fun _ => capture.val) (fun _ => delivery.val) := by
  intro actual report member _
  constructor
  · exact (EvidenceReportService.thinned_observation_mass capture delivery
      actual report member).symm.le
  · intro seen _ present
    exact (EvidenceReportService.thinned_delivery_mass capture delivery seen report present).symm.le

end Vegas.EventGraphRuntime.PhaseCount
