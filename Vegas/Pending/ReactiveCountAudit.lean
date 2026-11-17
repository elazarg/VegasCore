module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCountVerdict
public import Interaction.ReactiveTrafficContinuation
public import Interaction.ReactiveInputOrder
public import Interaction.ChallengeWindow
public import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

@[expose] public section

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

variable (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The count evidence of one traffic record: all signed envelopes of the
traffic and the record's packet. -/
def countEvidence (traffic : List ((reactiveApplication timeouts) leaks).TrafficRecord)
    (record : ((reactiveApplication timeouts) leaks).TrafficRecord) : CountEvidence graph :=
  (traffic.map ReactiveApplication.TrafficRecord.envelope, record.envelope)

/-- **The count audit.** A sample of count evidence is drawn from the actual
traffic; a player is charged once if some sampled packet of theirs is forbidden
by the count verdict. -/
def countAudit (sample : List (CountEvidence graph) → PMF (List (CountEvidence graph)))
    (traffic : List ((reactiveApplication timeouts) leaks).TrafficRecord) : PMF (Player → Bool) :=
  ((reactiveApplication timeouts) leaks).sampledTrafficAudit ((countEvidence timeouts) leaks
    traffic)
    (fun evidence => evidence.2.sender) (fun evidence => countPermits evidence.1 evidence.2)
    sample traffic

/-- Evidence lists witnessing a count violation by the given player. -/
def countViolation (who : Player) : Set (List (CountEvidence graph)) :=
  {items | ∃ item ∈ items, item.2.sender = who ∧ countPermits item.1 item.2 = false}

/-- On traffic with a violation by a player, observation covers some violation
by that player. Conditional on each such observation, a witness for that
player is delivered by the deadline. -/
def CountEvidenceCoverage (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ) : Prop :=
  ∀ actual who, actual ∈ countViolation who →
    observationRate who ≤ ((service.observations actual).toOuterMeasure
      (countViolation who)).toReal ∧
    ∀ seen ∈ (service.observations actual).support, seen ∈ countViolation who →
      deliveryRate who ≤ ((service.reports seen).toOuterMeasure {reports |
        EvidenceReport.deliveredEvidence
          (service.window.reportCutoff + service.window.inclusionBound) reports
            ∈ countViolation who}).toReal

/-- Per-item observation and delivery suffice for coverage by player. -/
theorem countEvidenceCoverage_of_item_bounds (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (bounds : ∀ actual item, item ∈ actual → countPermits item.1 item.2 = false →
      observationRate item.2.sender ≤
        ((service.observations actual).toOuterMeasure {seen | item ∈ seen}).toReal ∧
      ∀ seen ∈ (service.observations actual).support, item ∈ seen →
        deliveryRate item.2.sender ≤ ((service.reports seen).toOuterMeasure {reports |
          item ∈ EvidenceReport.deliveredEvidence
            (service.window.reportCutoff + service.window.inclusionBound) reports}).toReal) :
    CountEvidenceCoverage service observationRate deliveryRate := by
  have widen {α : Type} (law : PMF α) (read : α → List (CountEvidence graph))
      (item : CountEvidence graph) (bad : countPermits item.1 item.2 = false) :
      (law.toOuterMeasure {x | item ∈ read x}).toReal ≤
        (law.toOuterMeasure {x | read x ∈ countViolation item.2.sender}).toReal :=
    ENNReal.toReal_mono (outerMeasure_ne_top _ _) (law.toOuterMeasure_mono
      fun _ hx => ⟨item, hx.1, rfl, bad⟩)
  rintro actual who ⟨item, member, rfl, bad⟩
  constructor
  · exact ((bounds actual item member bad).1).trans (widen _ id item bad)
  · rintro seen supported ⟨other, present, owner, forbidden⟩
    have delivered := (bounds actual other
      (service.observations_authentic actual seen supported present) forbidden).2 seen
      supported present
    simpa only [owner] using delivered.trans (widen _ _ other forbidden)

/-- A forbidden packet in the actual traffic gives the product of observation
and conditional delivery coverage as a lower bound on its sender's collected
charge. -/
theorem countAudit_collection (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (traffic : List ((reactiveApplication timeouts) leaks).TrafficRecord)
    (record : ((reactiveApplication timeouts) leaks).TrafficRecord) (present : record ∈ traffic)
    (forbidden : countPermits (traffic.map ReactiveApplication.TrafficRecord.envelope)
      record.envelope = false) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      ((((countAudit timeouts) leaks service.sample traffic).map
        (fun verdict => verdict record.envelope.sender)) true).toReal := by
  unfold countAudit
  rw [ReactiveApplication.sampledTrafficAudit_collection]
  have member : (countEvidence timeouts) leaks traffic record ∈
      traffic.map ((countEvidence timeouts) leaks traffic) := List.mem_map_of_mem present
  obtain ⟨observed, delivered⟩ := coverage _ record.envelope.sender
    ⟨_, member, rfl, forbidden⟩
  apply service.sample_coverage _ (countViolation record.envelope.sender) _ _ _
    (delivery_nonnegative _) observed delivered
  rintro first last incl ⟨item, present, owner, bad⟩
  exact ⟨item, incl present, owner, bad⟩

/-- Traffic whose packets the count verdict all permits is charged to nobody. -/
theorem countAudit_charge_zero (service : EvidenceReportService (CountEvidence graph))
    (traffic : List ((reactiveApplication timeouts) leaks).TrafficRecord)
    (clean : ∀ record ∈ traffic,
      countPermits (traffic.map ReactiveApplication.TrafficRecord.envelope) record.envelope =
        true)
    (who : Player) :
    ((((countAudit timeouts) leaks service.sample traffic).map
      (fun verdict => verdict who)) true).toReal = 0 :=
  ((reactiveApplication timeouts) leaks).sampledTrafficAudit_sound _ _ _ _ traffic who
    (fun observed supported => service.sample_authentic _ observed supported)
    (fun record present _ => clean record present)

end Vegas.EventGraphRuntime
