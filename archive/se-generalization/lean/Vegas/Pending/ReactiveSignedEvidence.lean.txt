/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceAudit
import Vegas.Pending.ReactiveAsyncContract
import Interaction.ChallengeWindow
import Interaction.ReactiveTrafficState
import Interaction.ReactiveRawRoundTrace

/-! # Concrete signed content breaches and actual report collection

Malformed packets, withholding carrying evidence, commitments carrying opening evidence,
and uncertified openings cannot pass the settled content check. A named packet
may still be permitted before its event completes; complete settlement is an
explicit prerequisite for the final forbidden verdict.

Actual response traffic persists through arbitrary later policies. Observation
coverage and conditional report delivery during the challenge window bound
collection by their product, without independence or certain monitoring. These
are backend hypotheses on actual final evidence, separate from owner service.
Private binding material and certificate capability are not classified here.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Signed constructor content that no contract record can accept as settled
content. This predicate reads only the authenticated packet, never send time. -/
def SignedContentBreach (message : Message Player (WitnessedPacket graph)) : Prop :=
  message.payload.call.event? graph = none ∨
    (∃ event, message.payload.call = .withhold event ∧ message.payload.evidence ≠ none) ∨
    (∃ event candidate, message.payload.call = .commitment event candidate ∧
      message.payload.evidence ≠ none) ∨
    (∃ event candidate raw, message.payload.call = .opening event candidate raw ∧
      certifiedOpening message.payload = false)

theorem SignedContentBreach.not_settledContent
    {message : Message Player (WitnessedPacket graph)} (breach : SignedContentBreach message)
    (record : SettledRecord graph) : ¬ record.SettledContent message := by
  rcases breach with unnamed | ⟨event, withheld, evidence⟩ |
      ⟨event, candidate, committed, evidence⟩ | ⟨event, candidate, raw, opened, uncertified⟩
  · cases packet : message.payload.call with
    | commitment event candidate | opening event candidate raw | withhold event =>
        rw [packet] at unnamed
        cases unnamed
    | malformed raw =>
        unfold SettledRecord.SettledContent
        rw [packet]
        exact id
  · unfold SettledRecord.SettledContent
    rw [withheld]
    exact evidence
  · unfold SettledRecord.SettledContent
    rw [committed]
    exact fun content => evidence content.1
  · unfold SettledRecord.SettledContent
    rw [opened]
    intro content
    rw [uncertified] at content
    cases content.1

/-- This class is forbidden at every record that completed every event,
irrespective of which packets were accepted or what later players did. -/
theorem SignedContentBreach.forbidden_of_complete
    {message : Message Player (WitnessedPacket graph)} (breach : SignedContentBreach message)
    (record : SettledRecord graph)
    (complete : ∀ event, event ∈ record.view.observation.completionOrder) :
    record.permits message = false := by
  cases named : message.payload.call.event? graph with
  | none => exact SettledRecord.permits_eq_false_of_none record message named
  | some event =>
      exact SettledRecord.permits_eq_false_of_settled record message event named (complete event)
        (fun allowed => breach.not_settledContent record allowed.2)

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A signed content breach cannot be a fresh conforming canonical packet. -/
theorem SignedContentBreach.not_freshServiceEnvelope
    {message : Message Player (WitnessedPacket graph)} (breach : SignedContentBreach message)
    (view : PublicView graph) : ¬ runtime.freshServiceEnvelope view message := by
  intro conforms
  rcases breach with unnamed | ⟨event, withheld, evidence⟩ |
      ⟨event, candidate, committed, evidence⟩ | ⟨event, candidate, raw, opened, uncertified⟩
  · obtain ⟨event, named, _⟩ := runtime.freshServiceEnvelope_ready view message conforms
    rw [unnamed] at named
    cases named
  · simp only [freshServiceEnvelope, withheld] at conforms
    exact evidence conforms.2.2.1
  · simp only [freshServiceEnvelope, committed] at conforms
    exact evidence conforms.2.2.1
  · simp only [freshServiceEnvelope, opened] at conforms
    have certified := conforms.2.2.1
    rw [uncertified] at certified
    cases certified

/-- A complete actual application supplies the completion premise directly. -/
theorem SignedContentBreach.forbidden
    {message : Message Player (WitnessedPacket graph)} (breach : SignedContentBreach message)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (complete : execution.application.config.cut.Terminal) :
    (runtime.settledRecord leaks execution).permits message = false := by
  apply breach.forbidden_of_complete
  intro event
  apply (execution.application.config.history_exact event).mpr
  rw [complete]
  exact Finset.mem_univ event

/-- The packet's actual response record exists before any inclusion or watcher
sampling. It is derived from the real transition, not assumed as audit evidence. -/
theorem signed_response_traffic {initial : PMF (runtime.reactiveApplication leaks).State}
    {horizon remaining : Nat} {scheduler : (runtime.reactiveApplication leaks).Scheduler}
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (material : (runtime.reactiveApplication leaks).Submission)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩)) :
    (⟨execution.application.publicView, execution.network.ledger,
      ⟨(who, execution.network.nextSerial who), (runtime.reactiveApplication leaks).packet
        ((runtime.reactiveApplication leaks).submit execution.application who material) who
          (execution.network.known who) material⟩⟩ :
        (runtime.reactiveApplication leaks).TrafficRecord) ∈
      (runtime.reactiveApplication leaks).executionTraffic
        (execution.respond (runtime.reactiveApplication leaks) who ⟨some material⟩) := by
  let app := runtime.reactiveApplication leaks
  let history : (app.protocol initial horizon scheduler).History :=
    ⟨some ⟨remaining, some who, execution⟩, trace⟩
  have step : some ⟨remaining, none, execution.respond app who ⟨some material⟩⟩ ∈
      (app.transition initial horizon scheduler history.state
        (fun actor => if actor = who then some ⟨some material⟩ else none)).support := by
    dsimp only [history]
    change _ ∈ (PMF.pure _).support
    simp only [↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]
  have traffic := app.stateTraffic_transition initial horizon scheduler history _ _ step
  dsimp only [history] at traffic
  rw [app.trafficStep_submit] at traffic
  change _ ∈ app.stateTraffic
    (some ⟨remaining, none, execution.respond app who ⟨some material⟩⟩)
  rw [traffic]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Authentic observation and conditional delivery coverage for this actual
bad packet bound the collected charge at a complete final record. -/
theorem signedContentBreach_collection
    (service : EvidenceReportService
      (SettledRecord graph × Message Player (WitnessedPacket graph)))
    (control : (runtime.reactiveApplication leaks).Control)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).executionTraffic control.execution)
    (breach : SignedContentBreach record.envelope)
    (complete : control.execution.application.config.cut.Terminal)
    (observationRate deliveryRate : ℝ) (delivery_nonnegative : 0 ≤ deliveryRate)
    (observations :
      let actual := ((runtime.reactiveApplication leaks).executionTraffic control.execution).map
        (fun traffic => (runtime.settledRecord leaks control.execution, traffic.envelope))
      record ∈ (runtime.reactiveApplication leaks).executionTraffic control.execution →
        observationRate ≤ ((service.observations actual).toOuterMeasure {observed |
          (runtime.settledRecord leaks control.execution, record.envelope) ∈ observed}).toReal)
    (reports :
      let actual := ((runtime.reactiveApplication leaks).executionTraffic control.execution).map
        (fun traffic => (runtime.settledRecord leaks control.execution, traffic.envelope))
      ∀ observed ∈ (service.observations actual).support,
        (runtime.settledRecord leaks control.execution, record.envelope) ∈ observed →
        deliveryRate ≤ ((service.reports observed).toOuterMeasure {delivered |
          (runtime.settledRecord leaks control.execution, record.envelope) ∈
            EvidenceReport.deliveredEvidence
              (service.window.reportCutoff + service.window.inclusionBound) delivered}).toReal) :
    observationRate * deliveryRate ≤
      TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks fun settled =>
          (runtime.reactiveApplication leaks).sampledTrafficAudit
            (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
            (fun evidence => evidence.1.permits evidence.2) service.sample)
        (some control) record.envelope.sender := by
  let app := runtime.reactiveApplication leaks
  let evidence := (runtime.settledRecord leaks control.execution, record.envelope)
  let actual := (app.executionTraffic control.execution).map
    (fun traffic => (runtime.settledRecord leaks control.execution, traffic.envelope))
  have forbidden := breach.forbidden runtime leaks control.execution complete
  have covered := service.sample_coverage actual evidence observationRate deliveryRate
    delivery_nonnegative (observations present) reports
  have eventSubset : {observed : List (SettledRecord graph ×
      Message Player (WitnessedPacket graph)) | evidence ∈ observed} ⊆
      {observed | ∃ bad ∈ observed, bad.2.sender = record.envelope.sender ∧
        bad.1.permits bad.2 = false} := by
    intro observed member
    exact ⟨evidence, member, rfl, forbidden⟩
  have charged := ENNReal.toReal_mono (outerMeasure_ne_top (service.sample actual) _)
    ((service.sample actual).toOuterMeasure_mono (fun observed member => eventSubset member.1))
  have trafficBound := app.sampledTrafficAudit_collection
    (fun traffic => (runtime.settledRecord leaks control.execution, traffic.envelope))
    (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
    service.sample (app.executionTraffic control.execution) record.envelope.sender
  apply covered.trans
  have toTraffic := charged.trans (le_of_eq trafficBound.symm)
  exact toTraffic.trans (runtime.serviceAudit_charge_ge_traffic leaks (fun settled =>
    app.sampledTrafficAudit (fun traffic => (settled, traffic.envelope))
      (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
      service.sample) control record.envelope.sender)

variable [Fintype Player]

/-- One actual signed content breach gives the stated collection bound under
every subsequent behavioral profile. The complete-play service and challenge
coverage apply to the actual final record; no later policy is prescribed. -/
theorem signedContentBreach_collection_continuation
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (completes : CompletesPlay runtime leaks initial horizon scheduler)
    (service : EvidenceReportService
      (SettledRecord graph × Message Player (WitnessedPacket graph)))
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (long : 2 * horizon + 1 ≤ history.trace.length + fuel)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).stateTraffic history.state)
    (breach : SignedContentBreach record.envelope)
    (observationRate deliveryRate : ℝ) (delivery_nonnegative : 0 ≤ deliveryRate)
    (observations : ∀ actual (settled : SettledRecord graph),
      (settled, record.envelope) ∈ actual →
      observationRate ≤ ((service.observations actual).toOuterMeasure {observed |
        (settled, record.envelope) ∈ observed}).toReal)
    (reports : ∀ actual (settled : SettledRecord graph),
      ∀ observed ∈ (service.observations actual).support,
        (settled, record.envelope) ∈ observed →
        deliveryRate ≤ ((service.reports observed).toOuterMeasure {delivered |
          (settled, record.envelope) ∈ EvidenceReport.deliveredEvidence
            (service.window.reportCutoff + service.window.inclusionBound) delivered}).toReal) :
    observationRate * deliveryRate ≤
      ((((((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        (fun final => runtime.serviceAuditObservation leaks final.state)).bind
          (runtime.serviceAudit leaks fun settled =>
            (runtime.reactiveApplication leaks).sampledTrafficAudit
              (fun traffic => (settled, traffic.envelope)) (fun evidence => evidence.2.sender)
              (fun evidence => evidence.1.permits evidence.2) service.sample)).map
                (fun verdict => verdict record.envelope.sender)) true).toReal := by
  let app := runtime.reactiveApplication leaks
  let model := menu.information initial horizon scheduler
  let protocol := menu.protocol initial horizon scheduler
  rw [TerminalAudit.collection_probability]
  calc
    observationRate * deliveryRate =
        expect (model.runBehavioralFrom profile fuel history)
          (fun _ => observationRate * deliveryRate) := (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _)
        (TerminalAudit.payoffIntegrable_charge _ _ _ _)
      intro final supported
      have path := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser profile)
        fuel history final supported
      have kept : record ∈ app.stateTraffic final.state := by
        have persists := (menu.trafficAudit_reaches initial horizon scheduler path).subset
        rw [menu.trafficAudit_eq_stateTraffic, menu.trafficAudit_eq_stateTraffic] at persists
        exact persists present
      have stopped : app.terminal final.state := by
        rcases protocol.runRandomizedFor_terminal_or_length (model.randomizedChooser profile)
            fuel history final supported with terminal | length
        · exact terminal
        · have traceBound := app.trace_bound initial horizon scheduler
            (menu.toRawTrace initial horizon scheduler final.trace)
          rw [menu.toRawTrace_length] at traceBound
          have exhausted : app.rank horizon final.state = 0 := by omega
          exact (app.rank_zero horizon final.state).mp exhausted
      rcases final with ⟨state, trace⟩
      cases state with
      | none => exact stopped.elim
      | some control =>
          have rawTrace := menu.toRawTrace initial horizon scheduler trace
          have complete := completes control rawTrace stopped
          apply signedContentBreach_collection runtime leaks service control record kept breach
            complete observationRate deliveryRate delivery_nonnegative
          · intro actualRecord actualMember
            exact observations actualRecord _ (List.mem_map.mpr ⟨record, actualMember, rfl⟩)
          · exact reports _ _

end Vegas.EventGraphRuntime
