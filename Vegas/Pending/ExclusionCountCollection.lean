/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionCountMenu

/-! # Collection of forbidden recovery packets

The serial-order argument applies to the actual recovery traffic, including
packets emitted after exclusion. A forbidden packet retains its verdict under
every continuation, so authentic evidence coverage gives the same collection
bound against arbitrary later response policies.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A forbidden packet in the actual traffic gives the product of observation
and conditional delivery coverage as a lower bound on its sender's collected
charge. -/
theorem countAudit_collection (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (traffic : List (runtime.recoveryApplication leaks).TrafficRecord)
    (record : (runtime.recoveryApplication leaks).TrafficRecord) (present : record ∈ traffic)
    (forbidden : countPermits (traffic.map ReactiveApplication.TrafficRecord.envelope)
      record.envelope = false) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      (((countAudit runtime leaks service.sample traffic).map
        (fun verdict => verdict record.envelope.sender)) true).toReal := by
  unfold countAudit
  rw [ReactiveApplication.sampledTrafficAudit_collection]
  have member : countEvidence runtime leaks traffic record ∈
      traffic.map (countEvidence runtime leaks traffic) := List.mem_map_of_mem present
  obtain ⟨observed, delivered⟩ := coverage _ _ member forbidden
  refine (service.sample_coverage _ _ _ _ (delivery_nonnegative _) observed delivered).trans ?_
  apply ENNReal.toReal_mono (outerMeasure_ne_top _ _)
  apply PMF.toOuterMeasure_mono
  rintro seen ⟨included, _⟩
  exact ⟨_, included, rfl, forbidden⟩

end Vegas.EventGraphRuntime.Recovery
