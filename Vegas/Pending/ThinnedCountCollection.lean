/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveCountAudit
import Interaction.ThinnedEvidenceService

/-! # Imperfect observation and delivery for signed count evidence -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The count audit's coverage condition follows from the actual capture and
conditional delivery kernels, including evidence for packets never included. -/
theorem thinnedCountEvidence_coverage (capture delivery : Set.Icc (0 : ℝ) 1) :
    CountEvidenceCoverage
      (EvidenceReportService.thinned (Evidence := CountEvidence graph) capture delivery)
      (fun _ => capture.val) (fun _ => delivery.val) := by
  intro actual evidence member _
  constructor
  · exact (EvidenceReportService.thinned_observation_mass capture delivery
      actual evidence member).symm.le
  · intro seen _ present
    exact (EvidenceReportService.thinned_delivery_mass capture delivery
      seen evidence present).symm.le

end Vegas.EventGraphRuntime
