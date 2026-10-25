/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveCountVerdict
import Interaction.ReactiveTrafficContinuation
import Interaction.ReactiveInputOrder
import Interaction.ChallengeWindow
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # The count audit: sampled signed traffic judged by the count verdict

Settlement samples evidence from the actual traffic. Each item of evidence is a
packet together with the list of all signed envelopes, and the count verdict
judges the packet against the sender's lower-serial packets in that list. A
missed binding is not charged: it is an exclusion, handled by the payoffs.

The audit reads only the signed envelopes, in emission order
(`Vegas.EventGraphRuntime.countEvidence`). A forbidden packet in the actual
traffic bounds its sender's collected charge below by the product of
observation and conditional delivery coverage
(`Vegas.EventGraphRuntime.countAudit_collection`), and traffic whose packets
the count verdict all permits is charged to nobody
(`Vegas.EventGraphRuntime.countAudit_charge_zero`).

Every principal's inputs carry the serials `0, 1, …` in emission order, at
every legal prefix and under arbitrary responses. Hence a forbidden packet
stays forbidden along every continuation, and coverage of forbidden evidence
bounds the expected collection below under every later policy.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Count evidence: the signed envelopes of the traffic and one packet. -/
abbrev CountEvidence (graph : Vegas.EventGraph Player L) :=
  List (Message Player (WitnessedPacket graph)) × Message Player (WitnessedPacket graph)

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The count evidence of one traffic record: all signed envelopes of the
traffic and the record's packet. -/
def countEvidence (traffic : List (runtime.reactiveApplication leaks).TrafficRecord)
    (record : (runtime.reactiveApplication leaks).TrafficRecord) : CountEvidence graph :=
  (traffic.map ReactiveApplication.TrafficRecord.envelope, record.envelope)

/-- **The count audit.** A sample of count evidence is drawn from the actual
traffic; a player is charged once if some sampled packet of theirs is forbidden
by the count verdict. -/
def countAudit (sample : List (CountEvidence graph) → PMF (List (CountEvidence graph)))
    (traffic : List (runtime.reactiveApplication leaks).TrafficRecord) : PMF (Player → Bool) :=
  (runtime.reactiveApplication leaks).sampledTrafficAudit (runtime.countEvidence leaks traffic)
    (fun evidence => evidence.2.sender) (fun evidence => countPermits evidence.1 evidence.2)
    sample traffic

/-- Authentic backend coverage for count evidence the count verdict forbids.
Delivery is conditional on the entire observed list, allowing arbitrary
dependence between observation and censorship of reports. -/
def CountEvidenceCoverage (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ) : Prop :=
  ∀ actual evidence, evidence ∈ actual → countPermits evidence.1 evidence.2 = false →
    observationRate evidence.2.sender ≤
      ((service.observations actual).toOuterMeasure {seen | evidence ∈ seen}).toReal ∧
    ∀ seen ∈ (service.observations actual).support, evidence ∈ seen →
      deliveryRate evidence.2.sender ≤
        ((service.reports seen).toOuterMeasure {delivered |
          evidence ∈ EvidenceReport.deliveredEvidence
            (service.window.reportCutoff + service.window.inclusionBound) delivered}).toReal

/-- A forbidden packet in the actual traffic gives the product of observation
and conditional delivery coverage as a lower bound on its sender's collected
charge. -/
theorem countAudit_collection (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (traffic : List (runtime.reactiveApplication leaks).TrafficRecord)
    (record : (runtime.reactiveApplication leaks).TrafficRecord) (present : record ∈ traffic)
    (forbidden : countPermits (traffic.map ReactiveApplication.TrafficRecord.envelope)
      record.envelope = false) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      (((runtime.countAudit leaks service.sample traffic).map
        (fun verdict => verdict record.envelope.sender)) true).toReal := by
  unfold countAudit
  rw [ReactiveApplication.sampledTrafficAudit_collection]
  have member : runtime.countEvidence leaks traffic record ∈
      traffic.map (runtime.countEvidence leaks traffic) := List.mem_map_of_mem present
  obtain ⟨observed, delivered⟩ := coverage _ _ member forbidden
  refine (service.sample_coverage _ _ _ _ (delivery_nonnegative _) observed delivered).trans ?_
  apply ENNReal.toReal_mono (outerMeasure_ne_top _ _)
  apply PMF.toOuterMeasure_mono
  rintro seen ⟨included, _⟩
  exact ⟨_, included, rfl, forbidden⟩

/-- Traffic whose packets the count verdict all permits is charged to nobody. -/
theorem countAudit_charge_zero (service : EvidenceReportService (CountEvidence graph))
    (traffic : List (runtime.reactiveApplication leaks).TrafficRecord)
    (clean : ∀ record ∈ traffic,
      countPermits (traffic.map ReactiveApplication.TrafficRecord.envelope) record.envelope =
        true)
    (who : Player) :
    (((runtime.countAudit leaks service.sample traffic).map
      (fun verdict => verdict who)) true).toReal = 0 :=
  (runtime.reactiveApplication leaks).sampledTrafficAudit_sound _ _ _ _ traffic who
    (fun observed supported => service.sample_authentic _ observed supported)
    (fun record present _ => clean record present)

end Vegas.EventGraphRuntime
