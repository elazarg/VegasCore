/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountMenu

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

variable {runtime leaks}

/-- **A forbidden packet stays forbidden.** Along every legal continuation of
the complete runtime, a forbidden input remains an input and remains forbidden
by the count verdict on the later inputs. -/
theorem countForbidden_reaches {initial : PMF (phaseApplication runtime leaks).State}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {first last : ((phaseApplication runtime leaks).protocol initial horizon
      scheduler).History} {fuel : Nat}
    (path : ((phaseApplication runtime leaks).protocol initial horizon
      scheduler).ReachesWithin fuel first last)
    (before after : (phaseApplication runtime leaks).Control)
    (firstEq : first.state = some before) (lastEq : last.state = some after)
    (message : Message Player (CommitAttemptPacket graph))
    (present : message ∈ before.execution.network.inputs)
    (forbidden : permits before.execution.network.inputs message = false) :
    message ∈ after.execution.network.inputs ∧
      permits after.execution.network.inputs message = false := by
  let app := phaseApplication runtime leaks
  have traffic := app.stateTraffic_reaches initial horizon scheduler path
  have firstInputs := app.stateTraffic_inputs initial horizon scheduler first.trace
  have lastInputs := app.stateTraffic_inputs initial horizon scheduler last.trace
  have firstOrder := app.inputSerialsInOrder_history scheduler initial horizon first.trace
  have lastOrder := app.inputSerialsInOrder_history scheduler initial horizon last.trace
  rw [firstEq] at firstInputs firstOrder traffic
  rw [lastEq] at lastInputs lastOrder traffic
  have prefixOf : before.execution.network.inputs <+: after.execution.network.inputs := by
    have mapped := traffic.map ReactiveApplication.TrafficRecord.envelope
    rw [firstInputs, lastInputs] at mapped
    exact mapped
  refine ⟨prefixOf.subset present, ?_⟩
  rw [permits_congr after.execution.network.inputs before.execution.network.inputs message]
  · exact forbidden
  intro other
  constructor
  · rintro ⟨member, owner, lower⟩
    refine ⟨firstOrder.mem_of_prefix lastOrder prefixOf member ?_, owner, lower⟩
    rw [owner]
    exact lower.trans (firstOrder.serial_lt present)
  · rintro ⟨member, owner, lower⟩
    exact ⟨prefixOf.subset member, owner, lower⟩

variable [Fintype Player]

/-- A forbidden packet of `who` among the current inputs bounds `who`'s
expected collection below by the coverage product, under every later
behavioral profile of any response menu. -/
theorem countForbidden_collection_continuation
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (service : EvidenceReportService (Evidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : EvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (control : (phaseApplication runtime leaks).Control)
    (current : history.state = some control)
    (message : Message Player (CommitAttemptPacket graph))
    (present : message ∈ control.execution.network.inputs)
    (forbidden : permits control.execution.network.inputs message = false) :
    observationRate message.sender * deliveryRate message.sender ≤
      expect ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history)
        (fun final => TerminalAudit.charge (phaseApplication runtime leaks).stateTraffic
          (audit runtime leaks service.sample) final.state message.sender) := by
  let app := phaseApplication runtime leaks
  let model := menu.information initial horizon scheduler
  let protocol := menu.protocol initial horizon scheduler
  calc
    observationRate message.sender * deliveryRate message.sender =
        expect (model.runBehavioralFrom profile fuel history)
          (fun _ => observationRate message.sender * deliveryRate message.sender) :=
      (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _)
        (TerminalAudit.payoffIntegrable_charge _ _ _ _)
      intro final supported
      have path := menu.reaches_raw initial horizon scheduler
        (protocol.runRandomizedFor_reachesWithin (model.randomizedChooser profile) fuel history
          final supported)
      have traffic := app.stateTraffic_reaches initial horizon scheduler path
      change app.stateTraffic history.state <+: app.stateTraffic final.state at traffic
      rw [current] at traffic
      have currentInputs := app.stateTraffic_inputs initial horizon scheduler
        (menu.toRawTrace initial horizon scheduler history.trace)
      change (app.stateTraffic history.state).map ReactiveApplication.TrafficRecord.envelope =
        history.state.elim [] (fun control => control.execution.network.inputs) at currentInputs
      rw [current] at currentInputs
      obtain ⟨record, recorded, envelope⟩ := List.mem_map.mp (by rw [currentInputs]; exact present :
        message ∈ (app.stateTraffic (some control)).map ReactiveApplication.TrafficRecord.envelope)
      have kept : record ∈ app.stateTraffic final.state := traffic.subset recorded
      cases finalState : final.state with
      | none =>
          rw [finalState] at kept
          exact (List.not_mem_nil kept).elim
      | some after =>
          have retained := countForbidden_reaches path control after current finalState message
            present forbidden
          have finalInputs := app.stateTraffic_inputs initial horizon scheduler
            (menu.toRawTrace initial horizon scheduler final.trace)
          change (app.stateTraffic final.state).map ReactiveApplication.TrafficRecord.envelope =
            final.state.elim [] (fun control => control.execution.network.inputs) at finalInputs
          rw [finalState] at finalInputs kept
          have collected := audit_collection runtime leaks service observationRate
            deliveryRate delivery_nonnegative coverage (app.stateTraffic (some after)) record kept
            (by rw [finalInputs, envelope]; exact retained.2)
          rw [envelope] at collected
          exact collected


end Vegas.EventGraphRuntime.PhaseCount
