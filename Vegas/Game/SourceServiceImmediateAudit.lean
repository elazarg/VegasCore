/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCleanContinuation
import Vegas.Game.SourceServiceImmediateRecall
import Vegas.Game.SourceServiceAudit

/-! # Actual clean continuation after a legal clear owner decision

The same immediate policy starts from actual recall at any clear active owner
history of the risk menu, including histories with earlier silent deferrals.
Prefix packet soundness and answered activations are derived from that legal
history. Its response establishes binding-turn coverage for the raw suffix.
Every supported continuation within the horizon remains clear and every owner
packet passes the actual settled verdict. Authentic sampling collects no owner
charge. Other owners' suffix policies are arbitrary raw policies.

This establishes the clean continuation's audit behavior, not a source payoff
comparison, a collection lower bound for deviations or an equilibrium theorem.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The actual immediate continuation from a legal clear active owner prefix
has no owner risk or miss and permits every actual owner packet at each supported
scheduler boundary. Earlier prefix packets are included in the conclusion. -/
theorem sourceServiceImmediatePolicy_clean_continuation
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    {horizon remaining : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (profile : BehavioralProfile setup.program)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (follows : players who = serviceImmediatePolicy setup mode deadline leaks bound profile who)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      (execution.recall who) (execution.observe
          (serviceApplication setup mode deadline leaks) who)).support)
    (count : Nat) (within : count ≤ remaining) (next :
        (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).runRounds scheduler players count
      (execution.respond (serviceApplication setup mode deadline leaks) who response)).support) :
    (serviceRuntime setup mode deadline).serviceRisk leaks bound who (next.recall who)
        (next.observe (serviceApplication setup mode deadline leaks) who) = false ∧
      next.application.publicView.missedBindingBy who = false ∧
      (∀ record ∈ (serviceApplication setup mode deadline leaks).executionTraffic next,
          record.envelope.sender = who →
        ((serviceRuntime setup mode deadline).settledRecord leaks next).permits record.envelope =
            true) := by
  let app := serviceApplication setup mode deadline leaks
  let menu := bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound
  let start := execution.respond app who response
  have components :=
      ((serviceRuntime setup mode deadline).serviceRisk_clear_iff leaks bound who _ _).mp clear
  obtain ⟨atTurn, slots⟩ := riskCanonicalSlots_history bounds bound _ trace who components.1
  have rawTrace := menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler trace
  have turned := sourceServiceImmediatePolicy_bindingTurnsRecorded_respond rawTrace atTurn slots
    clear response chosen
  have available := sourceServiceImmediatePolicy_risk_retained bounds covered initialCovered
    capacity bound profile who permitted _ trace response chosen
  obtain ⟨menuStart⟩ := menu.trace_respond
      (serviceInitialLaw setup mode) horizon scheduler remaining execution
    who response trace available
  have supportedStart := menu.roundSupported_uniform
      (serviceInitialLaw setup mode) horizon scheduler menuStart
  have answered := roundsFrom_activationsAnswered start.environmentRecall.length start
    supportedStart.2
  have traceStart := menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler menuStart
  have persistentClear :
      (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who (start.recall who)
      (start.observe app who) = false :=
    ((serviceRuntime setup mode deadline).persistentServiceRisk_respond_protected leaks bound
        execution who response
      (sourceServiceImmediatePolicy_submissionFits chosen) components.2).trans components.1
  have clearStart := (serviceRuntime setup mode deadline).serviceRisk_clear leaks bound who
      (start.recall who)
    (start.observe app who) persistentClear
    (recordedBindings_currentOpportunity_clear contract timely traceStart answered who turned)
  obtain ⟨atStart, slotsStart, callsStart, conformStart, onceStart, goodStart⟩ :=
    sourceServiceImmediatePolicy_packetFacts_after_prefix_response bounds contract who profile
      execution trace clear response chosen
  have traceBudget : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨(remaining - count) + count, none, start⟩) := by
    simpa only [Nat.sub_add_cancel within] using traceStart
  obtain ⟨_, _, clearNext, _, _, _, _, _, goodNext⟩ :=
    sourceServiceImmediatePolicy_continuationFacts_runRounds contract timely players who profile
      follows count start next traceBudget answered turned clearStart atStart slotsStart callsStart
      conformStart onceStart goodStart reached
  have noMiss :=
      ((serviceRuntime setup mode deadline).persistentServiceRisk_clear_iff leaks bound who _ _).mp
    (((serviceRuntime setup mode deadline).serviceRisk_clear_iff leaks bound who _ _).mp
        clearNext).1 |>.1.1
  refine ⟨clearNext, noMiss, ?_⟩
  obtain ⟨nextTrace⟩ := app.raw_trace_runRounds
      (serviceInitialLaw setup mode) horizon scheduler players
    (remaining - count) count start next traceBudget reached
  have inputs := app.stateTraffic_inputs (serviceInitialLaw setup mode) horizon scheduler nextTrace
  change (app.executionTraffic next).map ReactiveApplication.TrafficRecord.envelope =
    next.network.inputs at inputs
  intro record member authored
  have emitted : Emitted setup leaks next record.envelope := by
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  exact (goodNext record.envelope authored emitted).permits

/-- Authentic sampling collects zero owner charge throughout the actual
immediate continuation, including at the final remaining-round boundary. -/
theorem sourceServiceImmediatePolicy_audit_clear_after_prefix_response
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    {horizon remaining : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (profile : BehavioralProfile setup.program)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (follows : players who = serviceImmediatePolicy setup mode deadline leaks bound profile who)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      (execution.recall who) (execution.observe
          (serviceApplication setup mode deadline leaks) who)).support)
    (count : Nat) (within : count ≤ remaining) (next :
        (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).runRounds scheduler players count
      (execution.respond (serviceApplication setup mode deadline leaks) who response)).support)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
      (serviceSourceAudit setup mode deadline leaks sample) (some ⟨remaining - count, none,
          next⟩) who = 0 := by
  obtain ⟨_, noMiss, permits⟩ := sourceServiceImmediatePolicy_clean_continuation bounds covered
    initialCovered capacity contract timely players who profile permitted follows execution trace
    clear response chosen count within next reached
  unfold serviceSourceAudit
  rw [(serviceRuntime setup mode deadline).serviceAudit_charge, noMiss]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply (serviceApplication setup mode deadline leaks).sampledTrafficAudit_sound
  · exact authentic _
  · exact permits

end Vegas
