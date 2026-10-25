/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountMenu
import Interaction.CompleteEvidenceService

/-! # Collection of forbidden attempt-addressed packets

The serial-order argument applies to the actual phased traffic, including
packets emitted after exclusion. A forbidden packet retains its verdict under
every continuation, so authentic evidence coverage gives the same collection
bound against arbitrary later response policies.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Conditional observation and delivery coverage for the actual forbidden
signed attempt evidence. Delivery is conditional on the entire observed list. -/
def EvidenceCoverage (service : EvidenceReportService (Evidence graph))
    (observationRate deliveryRate : Player → ℝ) : Prop :=
  ∀ actual report, report ∈ actual → permits report.1 report.2 = false →
    observationRate report.2.sender ≤
      ((service.observations actual).toOuterMeasure {seen | report ∈ seen}).toReal ∧
    ∀ seen ∈ (service.observations actual).support, report ∈ seen →
      deliveryRate report.2.sender ≤
        ((service.reports seen).toOuterMeasure {delivered |
          report ∈ EvidenceReport.deliveredEvidence
            (service.window.reportCutoff + service.window.inclusionBound) delivered}).toReal

/-- Complete authentic observation and immediate delivery give unit coverage. -/
theorem completeEvidence_coverage :
    EvidenceCoverage (EvidenceReportService.complete (Evidence graph))
      (fun _ => 1) (fun _ => 1) := by
  intro actual report member _
  constructor
  · exact (EvidenceReportService.complete_observation_mass actual report member).symm.le
  · intro seen _ present
    exact (EvidenceReportService.complete_delivery_mass seen report present).symm.le

/-- A forbidden packet in the actual traffic gives the product of observation
and conditional delivery coverage as a lower bound on its sender's collected
charge. -/
theorem audit_collection (service : EvidenceReportService (Evidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : EvidenceCoverage service observationRate deliveryRate)
    (traffic : List (phaseApplication runtime leaks).TrafficRecord)
    (record : (phaseApplication runtime leaks).TrafficRecord) (present : record ∈ traffic)
    (forbidden : permits (traffic.map ReactiveApplication.TrafficRecord.envelope)
      record.envelope = false) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      (((audit runtime leaks service.sample traffic).map
        (fun verdict => verdict record.envelope.sender)) true).toReal := by
  unfold audit
  rw [ReactiveApplication.sampledTrafficAudit_collection]
  have member : evidence runtime leaks traffic record ∈
      traffic.map (evidence runtime leaks traffic) := List.mem_map_of_mem present
  obtain ⟨observed, delivered⟩ := coverage _ _ member forbidden
  refine (service.sample_coverage _ _ _ _ (delivery_nonnegative _) observed delivered).trans ?_
  apply ENNReal.toReal_mono (outerMeasure_ne_top _ _)
  apply PMF.toOuterMeasure_mono
  rintro seen ⟨included, _⟩
  exact ⟨_, included, rfl, forbidden⟩

end Vegas.EventGraphRuntime.PhaseCount
