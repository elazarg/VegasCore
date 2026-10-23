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

variable {runtime leaks}

/-- **A forbidden packet stays forbidden.** Along every legal continuation of
the complete runtime, a forbidden input remains an input and remains forbidden
by the count verdict on the later inputs. -/
theorem countForbidden_reaches {initial : PMF (runtime.recoveryApplication leaks).State}
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {first last : ((runtime.recoveryApplication leaks).protocol initial horizon
      scheduler).History} {fuel : Nat}
    (path : ((runtime.recoveryApplication leaks).protocol initial horizon
      scheduler).ReachesWithin fuel first last)
    (before after : (runtime.recoveryApplication leaks).Control)
    (firstEq : first.state = some before) (lastEq : last.state = some after)
    (message : Message Player (WitnessedPacket graph))
    (present : message ∈ before.execution.network.inputs)
    (forbidden : countPermits before.execution.network.inputs message = false) :
    message ∈ after.execution.network.inputs ∧
      countPermits after.execution.network.inputs message = false := by
  let app := runtime.recoveryApplication leaks
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
  rw [countPermits_congr after.execution.network.inputs before.execution.network.inputs message]
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
    (menu : (runtime.recoveryApplication leaks).ResponseMenu)
    (initial : PMF (runtime.recoveryApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (control : (runtime.recoveryApplication leaks).Control)
    (current : history.state = some control)
    (message : Message Player (WitnessedPacket graph))
    (present : message ∈ control.execution.network.inputs)
    (forbidden : countPermits control.execution.network.inputs message = false) :
    observationRate message.sender * deliveryRate message.sender ≤
      expect ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history)
        (fun final => TerminalAudit.charge (runtime.recoveryApplication leaks).stateTraffic
          (countAudit runtime leaks service.sample) final.state message.sender) := by
  let app := runtime.recoveryApplication leaks
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
          have collected := countAudit_collection runtime leaks service observationRate
            deliveryRate delivery_nonnegative coverage (app.stateTraffic (some after)) record kept
            (by rw [finalInputs, envelope]; exact retained.2)
          rw [envelope] at collected
          exact collected


end Vegas.EventGraphRuntime.Recovery
