/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSignedEvidence

/-! # Authentic collection of evidence forbidden by the final record

Coverage is stated for actual signed evidence that the public settled record
forbids. The observer may miss packets, observations may be correlated, and
report delivery is conditional on the complete observed list. No send-time
oracle or certain watcher is required.

A persisted packet yields a continuation bound when its actual final verdict
is forbidden. Establishing that verdict remains an operational obligation;
constructor-level signed content breaches discharge it under complete play.
Private binding material and certificate capability are separate questions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Authentic backend coverage for forbidden evidence in the actual final
record. Delivery is conditional on the entire observed list, allowing arbitrary
dependence between observation and censorship of reports. -/
def FinalForbiddenEvidenceCoverage
    (service : EvidenceReportService
      (SettledRecord graph × Message Player (WitnessedPacket graph)))
    (observationRate deliveryRate : Player → ℝ) : Prop :=
  ∀ actual evidence, evidence ∈ actual → evidence.1.permits evidence.2 = false →
    observationRate evidence.2.sender ≤
      ((service.observations actual).toOuterMeasure {seen | evidence ∈ seen}).toReal ∧
    ∀ seen ∈ (service.observations actual).support, evidence ∈ seen →
      deliveryRate evidence.2.sender ≤
        ((service.reports seen).toOuterMeasure {delivered |
          evidence ∈ EvidenceReport.deliveredEvidence
            (service.window.reportCutoff + service.window.inclusionBound) delivered}).toReal

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- An actual packet forbidden by the final record gives the product of
observation and conditional delivery coverage as a lower bound on the real
one-time collected charge. Other detected breaches may increase that charge. -/
theorem settledPacket_collection
    (service : EvidenceReportService
      (SettledRecord graph × Message Player (WitnessedPacket graph)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage service observationRate deliveryRate)
    (control : (runtime.reactiveApplication leaks).Control)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).executionTraffic control.execution)
    (forbidden : (runtime.settledRecord leaks control.execution).permits record.envelope = false) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks fun settled =>
          (runtime.reactiveApplication leaks).sampledTrafficAudit
            (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
            (fun evidence => evidence.1.permits evidence.2) service.sample)
        (some control) record.envelope.sender := by
  apply runtime.serviceAudit_charge_from_record leaks
    (Evidence := SettledRecord graph × Message Player (WitnessedPacket graph))
    (fun settled traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
    (fun evidence => evidence.1.permits evidence.2) service.sample record.envelope.sender
    (observationRate record.envelope.sender * deliveryRate record.envelope.sender) ?_
    control record present rfl forbidden
  intro actual evidence member owned bad
  obtain ⟨observed, delivered⟩ := coverage actual evidence member bad
  have collected := service.sample_coverage actual evidence
    (observationRate evidence.2.sender) (deliveryRate evidence.2.sender)
    (delivery_nonnegative evidence.2.sender) observed delivered
  simpa only [owned] using collected

/-- Complete application play supplies the final forbidden verdict for a
constructor-level signed breach. Coverage need only apply to forbidden final
evidence, rather than every possible intermediate record. -/
theorem signedContentBreach_collection_of_finalCoverage
    (service : EvidenceReportService
      (SettledRecord graph × Message Player (WitnessedPacket graph)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage service observationRate deliveryRate)
    (control : (runtime.reactiveApplication leaks).Control)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).executionTraffic control.execution)
    (breach : SignedContentBreach record.envelope)
    (complete : control.execution.application.config.cut.Terminal) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks fun settled =>
          (runtime.reactiveApplication leaks).sampledTrafficAudit
            (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
            (fun evidence => evidence.1.permits evidence.2) service.sample)
        (some control) record.envelope.sender :=
  runtime.settledPacket_collection leaks service observationRate deliveryRate
    delivery_nonnegative coverage control record present
    (breach.forbidden runtime leaks control.execution complete)

variable [Fintype Player]

/-- If every final state of a continuation carries some actual packet of `who`
that its settled record forbids, the product of observation and conditional
delivery coverage bounds the expected one-time collection from `who`. The
forbidden packet may differ between final states. -/
theorem forbiddenTraffic_collection_continuation
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (service : EvidenceReportService
      (SettledRecord graph × Message Player (WitnessedPacket graph)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History) (who : Player)
    (forbidden : ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralFrom
      profile fuel history).support,
      ∃ control, final.state = some control ∧
        ∃ record ∈ (runtime.reactiveApplication leaks).executionTraffic control.execution,
          record.envelope.sender = who ∧
          (runtime.settledRecord leaks control.execution).permits record.envelope = false) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history)
        (fun final => TerminalAudit.charge (runtime.serviceAuditObservation leaks)
          (runtime.serviceAudit leaks fun settled =>
            (runtime.reactiveApplication leaks).sampledTrafficAudit
              (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
              (fun evidence => evidence.1.permits evidence.2) service.sample)
          final.state who) := by
  let model := menu.information initial horizon scheduler
  calc
    observationRate who * deliveryRate who =
        expect (model.runBehavioralFrom profile fuel history)
          (fun _ => observationRate who * deliveryRate who) := (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _)
        (TerminalAudit.payoffIntegrable_charge _ _ _ _)
      intro final supported
      obtain ⟨control, current, record, present, authored, rejected⟩ :=
        forbidden final supported
      have collected := runtime.settledPacket_collection leaks service observationRate
        deliveryRate delivery_nonnegative coverage control record present rejected
      rw [authored] at collected
      rw [current]
      exact collected

/-- Actual traffic persists under every later behavioral profile. The final
packet verdict is the explicit operational premise; no payoff comparison or
prescribed continuation is assumed. -/
theorem settledPacket_collection_continuation
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (service : EvidenceReportService
      (SettledRecord graph × Message Player (WitnessedPacket graph)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).stateTraffic history.state)
    (forbidden : ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralFrom
      profile fuel history).support,
      ∀ control, final.state = some control →
        (runtime.settledRecord leaks control.execution).permits record.envelope = false) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      expect ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history)
        (fun final => TerminalAudit.charge (runtime.serviceAuditObservation leaks)
          (runtime.serviceAudit leaks fun settled =>
            (runtime.reactiveApplication leaks).sampledTrafficAudit
              (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
              (fun evidence => evidence.1.permits evidence.2) service.sample)
          final.state record.envelope.sender) := by
  let app := runtime.reactiveApplication leaks
  let model := menu.information initial horizon scheduler
  let protocol := menu.protocol initial horizon scheduler
  apply runtime.forbiddenTraffic_collection_continuation leaks menu initial horizon scheduler
    service observationRate deliveryRate delivery_nonnegative coverage profile fuel history
  intro final supported
  have path := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser profile)
    fuel history final supported
  have kept : record ∈ app.stateTraffic final.state := by
    have persists := (menu.trafficAudit_reaches initial horizon scheduler path).subset
    rw [menu.trafficAudit_eq_stateTraffic, menu.trafficAudit_eq_stateTraffic] at persists
    exact persists present
  cases current : final.state with
  | none =>
      rw [current] at kept
      exact (List.not_mem_nil kept).elim
  | some control =>
      refine ⟨control, rfl, record, ?_, rfl, forbidden final supported control current⟩
      simpa only [current, ReactiveApplication.stateTraffic] using kept

/-- Under complete play, bounded termination derives the final forbidden
verdict for an actual signed content breach under arbitrary later policies.
The same final-record backend coverage suffices. -/
theorem signedContentBreach_collection_continuation_of_finalCoverage
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (completes : CompletesPlay runtime leaks initial horizon scheduler)
    (service : EvidenceReportService
      (SettledRecord graph × Message Player (WitnessedPacket graph)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (long : 2 * horizon + 1 ≤ history.trace.length + fuel)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).stateTraffic history.state)
    (breach : SignedContentBreach record.envelope) :
    observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
      expect ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history)
        (fun final => TerminalAudit.charge (runtime.serviceAuditObservation leaks)
          (runtime.serviceAudit leaks fun settled =>
            (runtime.reactiveApplication leaks).sampledTrafficAudit
              (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
              (fun evidence => evidence.1.permits evidence.2) service.sample)
          final.state record.envelope.sender) := by
  let app := runtime.reactiveApplication leaks
  let model := menu.information initial horizon scheduler
  let protocol := menu.protocol initial horizon scheduler
  apply runtime.settledPacket_collection_continuation leaks menu initial horizon scheduler
    service observationRate deliveryRate delivery_nonnegative coverage profile fuel history
    record present
  intro final supported control current
  have stopped : app.terminal final.state := by
    rcases protocol.runRandomizedFor_terminal_or_length (model.randomizedChooser profile)
        fuel history final supported with terminal | length
    · exact terminal
    · have traceBound := app.trace_bound initial horizon scheduler
        (menu.toRawTrace initial horizon scheduler final.trace)
      rw [menu.toRawTrace_length] at traceBound
      have exhausted : app.rank horizon final.state = 0 := by omega
      exact (app.rank_zero horizon final.state).mp exhausted
  have rawTrace : (app.protocol initial horizon scheduler).Trace (some control) :=
    current ▸ menu.toRawTrace initial horizon scheduler final.trace
  have complete := completes control rawTrace (current ▸ stopped)
  exact breach.forbidden runtime leaks control.execution complete

end Vegas.EventGraphRuntime
