/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveWithholdingReceipts
import Vegas.Pending.ReactiveSettledCollection
import Vegas.Game.SourceServiceAudit
import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Game.SourceServiceDecidedCompletion
import Interaction.ReactiveMenuContinuation
import GameTheoryExtensions.Analysis.Protocol.TerminalAuditContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Withholding bounds a public guessing payoff under arbitrary continuation

The score reads one actual publication result and a fixed initial parameter.
If the first withholding envelope is accepted, its public result is permanently
LOW. If it is never accepted, its settled verdict is forbidden and authentic
collection covers the full score range. The later player policies are arbitrary.
This does not identify incoming beliefs or construct a source equilibrium.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A bounded public guessing score; success is HIGH and failure is LOW.
The initial parameter is retained as the same external carrier coordinate. -/
def sourcePublicationGuessValue (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload) (high : Bool)
    (state : (application setup leaks).ProtocolState) : ℝ :=
  state.elim 0 fun control => (control.execution.application.config.outputs event).elim 0
    fun result => if (cast (congrArg EventField.Value outputEq) result).isSuccess = high
      then 1 else 0

theorem sourcePublicationGuessValue_mem_Icc (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload) (high : Bool)
    (state : (application setup leaks).ProtocolState) :
    sourcePublicationGuessValue setup leaks event payload outputEq high state ∈ Set.Icc 0 1 := by
  unfold sourcePublicationGuessValue
  cases state with
  | none => norm_num
  | some control =>
      cases output : control.execution.application.config.outputs event <;>
        simp only [output, Option.elim_none, Option.elim_some]
      · norm_num
      · split_ifs <;> norm_num

/-- At an actual settled endpoint, THIS first withholding either fixes LOW
or is forbidden with the backend's collection lower bound. -/
theorem sourceService_withhold_failure_or_collection {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (record : (application setup leaks).TrafficRecord)
    (present : record ∈ (application setup leaks).executionTraffic control.execution)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (call : record.envelope.payload.call = .withhold event)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    control.execution.application.config.outputs event = some
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload))) ∨
      observationRate record.envelope.sender * deliveryRate record.envelope.sender ≤
        TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks backend.sample) (some control)
            record.envelope.sender := by
  by_cases accepted : (record.envelope.id, true) ∈ control.execution.receipts
  · left
    have rawTrace := trace
    rw [initialLaw_eq_inputs] at rawTrace
    have inputs := (application setup leaks).stateTraffic_inputs (initialLaw setup) horizon
      scheduler trace
    change ((application setup leaks).executionTraffic control.execution).map
      ReactiveApplication.TrafficRecord.envelope = control.execution.network.inputs at inputs
    have emitted : record.envelope ∈ control.execution.network.inputs := by
      rw [← inputs]
      exact List.mem_map.mpr ⟨record, present, rfl⟩
    exact (runtime setup).withhold_receipt_output_failure leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler control rawTrace record.envelope
      emitted accepted event payload outputEq call
  · right
    have named : record.envelope.payload.call.event? (graph setup) = some event := by
      rw [call]
      rfl
    have forbidden := SettledRecord.permits_eq_false_of_settled
      ((runtime setup).settledRecord leaks control.execution) record.envelope event named
      ((control.execution.application.config.history_exact event).mpr completed)
      (fun permitted => accepted permitted.1)
    exact (runtime setup).settledPacket_collection leaks backend observationRate deliveryRate
      delivery_nonnegative coverage control record present forbidden

/-- The actual audited guessing payoff after a first withholding is at most
the LOW-correct indicator. This bound permits every later raw response. -/
theorem sourceService_withhold_guess_value_le {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (record : (application setup leaks).TrafficRecord)
    (present : record ∈ (application setup leaks).executionTraffic control.execution)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (call : record.envelope.payload.call = .withhold event)
    (completed : event ∈ control.execution.application.config.cut.completed)
    (high : Bool) (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit record.envelope.sender)
    (sufficient : 1 ≤ observationRate record.envelope.sender *
      deliveryRate record.envelope.sender * deposit record.envelope.sender) :
    TerminalAudit.utility
      (fun state _ => sourcePublicationGuessValue setup leaks event payload outputEq high state)
      ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks backend.sample)
      deposit (some control) record.envelope.sender ≤ if high then 0 else 1 := by
  have chargeNonnegative := (TerminalAudit.charge_mem_Icc
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks backend.sample)
    (some control) record.envelope.sender).1
  rcases sourceService_withhold_failure_or_collection setup leaks control trace backend
      observationRate deliveryRate delivery_nonnegative coverage record present event payload
      outputEq call completed with failure | collection
  · have value : sourcePublicationGuessValue setup leaks event payload outputEq high
        (some control) = if high then 0 else 1 := by
      cases high <;> simp [sourcePublicationGuessValue, failure, PublicationResult.isSuccess]
    simp only [TerminalAudit.utility]
    rw [value]
    exact sub_le_self _ (mul_nonneg chargeNonnegative nonnegative)
  · have bound := (sourcePublicationGuessValue_mem_Icc setup leaks event payload outputEq high
      (some control)).2
    have collected := (mul_le_mul_of_nonneg_right collection nonnegative)
    simp only [TerminalAudit.utility]
    have low : (0 : ℝ) ≤ if high then 0 else 1 := by cases high <;> norm_num
    linarith

variable [Fintype Player]

open Classical in
/-- Once the actual first withholding record is present, every whole native
continuation has guessing value at most the LOW-correct initial indicator.
Completion and traffic persistence are derived from the existing evaluator. -/
theorem sourceService_withhold_guess_continuation_le
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (profile : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (backend : EvidenceReportService (SettledEvidence setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (record : (application setup leaks).TrafficRecord)
    (present : record ∈ (application setup leaks).stateTraffic history.state)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (call : record.envelope.payload.call = .withhold event)
    (high : Bool) (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit record.envelope.sender)
    (sufficient : 1 ≤ observationRate record.envelope.sender *
      deliveryRate record.envelope.sender * deposit record.envelope.sender) :
    expect ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
      (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories profile history)
      (fun final => TerminalAudit.utility
        (fun state _ => sourcePublicationGuessValue setup leaks event payload outputEq high state)
        ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks backend.sample) deposit final.state
        record.envelope.sender) ≤ if high then 0 else 1 := by
  let app := application setup leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let protocol := menu.protocol (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let fuel := 2 * horizon + 1 - history.trace.length
  have runner := model.runBehavioralTerminalFrom_eq_remaining certificate profile
    (menu.bounded (initialLaw setup) horizon scheduler) history
  rw [runner]
  let law := model.runBehavioralFrom profile fuel history
  have baseIntegrable : PayoffIntegrable law (fun final =>
      sourcePublicationGuessValue setup leaks event payload outputEq high final.state) := by
    apply payoffIntegrable_of_bounded _ _ (C := 1)
    intro final
    have bounds := sourcePublicationGuessValue_mem_Icc setup leaks event payload outputEq high
      final.state
    rw [abs_of_nonneg bounds.1]
    exact bounds.2
  apply expect_le_const law _ (TerminalAudit.payoffIntegrable_utility law
    (fun final _ => sourcePublicationGuessValue setup leaks event payload outputEq high final.state)
    (fun final => (runtime setup).serviceAuditObservation leaks final.state)
    (sourceServiceAudit setup leaks backend.sample) deposit record.envelope.sender baseIntegrable)
  intro final supported
  have terminal : app.terminal final.state :=
    model.runBehavioralTerminalFrom_support_terminal certificate profile history final
      (by rw [runner]; exact supported)
  have path := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser profile)
    fuel history final supported
  have kept := (menu.trafficAudit_reaches (initialLaw setup) horizon scheduler path).subset
  rw [menu.trafficAudit_eq_stateTraffic, menu.trafficAudit_eq_stateTraffic] at kept
  have keptRecord := kept present
  cases current : final.state with
  | none =>
      rw [current] at keptRecord
      exact (List.not_mem_nil keptRecord).elim
  | some control =>
      have trace := current ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
      have complete := completes control trace (current ▸ terminal)
      have completed : event ∈ control.execution.application.config.cut.completed := by
        rw [complete]
        exact Finset.mem_univ event
      have bound := sourceService_withhold_guess_value_le setup leaks control trace backend
        observationRate
        deliveryRate delivery_nonnegative coverage record
        (by simpa only [current, ReactiveApplication.stateTraffic] using keptRecord)
        event payload outputEq call completed high deposit nonnegative sufficient
      simpa only [TerminalAudit.utility, TerminalAudit.charge, current] using bound

end Vegas
