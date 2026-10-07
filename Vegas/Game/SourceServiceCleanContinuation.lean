/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Game.SourceServiceImmediatePolicy
import Vegas.Game.SourceServiceRiskPrefix
import Vegas.Game.SourceServiceImmediateRisk

/-! # Packet soundness through a continuation from an actual prefix

The packet invariants concern one owner only. Foreign responses are arbitrary.
An owner's first conforming protected call extends the actual recall and
retains the good content of every earlier packet. Service commands use the
contract's sole-call inclusion guarantee and the actual settled record.
These facts do not establish an incentive comparison.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The same response also preserves all actual packets' good settled content.
The prefix facts are local invariants, not an assumed continuation payoff law. -/
theorem ownerPacketFacts_respond {bound : (serviceGraph setup mode).EventId → Nat}
    (execution : (serviceApplication setup mode deadline leaks).Execution) (who : Player)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (facts : SettledFacts setup leaks execution)
    (calls : OwnFreshCalls setup leaks bound execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (good : ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message)
    (first : (serviceRuntime setup mode deadline).firstSubmission leaks
        (execution.recall who) response = true)
    (fresh : ∀ material, response.transmission = some material →
      (serviceRuntime setup mode deadline).freshServiceEnvelope execution.application.publicView
        ⟨(who, execution.network.nextSerial who),
          (serviceApplication setup mode deadline leaks).packet
              ((serviceApplication setup mode deadline leaks).submit
            execution.application who material) who (execution.network.known who) material⟩)
    (fits : ∀ event, (serviceRuntime setup mode deadline).submittedEvent? leaks response =
        some event →
      execution.application.publicView.InclusionFitsDeadline
          (serviceRuntime setup mode deadline) bound event) :
    OwnFreshCalls setup leaks bound
        (execution.respond (serviceApplication setup mode deadline leaks) who response) who ∧
      FreshCallsConform setup leaks (execution.respond
          (serviceApplication setup mode deadline leaks) who response)
        who ∧
      OneCallPerEvent setup leaks (execution.respond
          (serviceApplication setup mode deadline leaks) who response)
        who ∧
      (∀ message, message.sender = who →
        Emitted setup leaks (execution.respond
            (serviceApplication setup mode deadline leaks) who response) message →
        SettledGood setup leaks (execution.respond
            (serviceApplication setup mode deadline leaks) who response)
          message) := by
  obtain ⟨callsNext, conformNext, onceNext⟩ := ownerCallFacts_respond execution who response calls
    conform once first fresh fits
  exact ⟨callsNext, conformNext, onceNext,
    owner_good_response facts who who response good (fun _ => fresh)⟩

/-- An arbitrary foreign response preserves the selected owner's packet facts. -/
theorem ownerPacketFacts_respond_other {bound : (serviceGraph setup mode).EventId → Nat}
    (execution : (serviceApplication setup mode deadline leaks).Execution) (who responder : Player)
    (different : who ≠ responder) (response : (serviceApplication setup mode deadline leaks).Action)
    (facts : SettledFacts setup leaks execution)
    (calls : OwnFreshCalls setup leaks bound execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (good : ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message) :
    OwnFreshCalls setup leaks bound
        (execution.respond (serviceApplication setup mode deadline leaks) responder response) who ∧
      FreshCallsConform setup leaks
        (execution.respond (serviceApplication setup mode deadline leaks) responder response) who ∧
      OneCallPerEvent setup leaks
        (execution.respond (serviceApplication setup mode deadline leaks) responder response) who ∧
      (∀ message, message.sender = who →
        Emitted setup leaks (execution.respond
            (serviceApplication setup mode deadline leaks) responder response)
          message →
        SettledGood setup leaks (execution.respond
            (serviceApplication setup mode deadline leaks) responder response)
          message) := by
  have recallEq :=
      (serviceApplication setup mode deadline leaks).respond_recall_other execution responder who
    different response
  refine ⟨?_, ?_, ?_, owner_good_response facts who responder response good
    (fun same => (different same.symm).elim)⟩
  · unfold OwnFreshCalls
    rw [recallEq]
    exact calls
  · unfold FreshCallsConform
    rw [recallEq]
    exact conform
  · unfold OneCallPerEvent
    rw [recallEq]
    exact once

/-- A service command preserves the owner's packet facts at an actual raw
trace. No assertion about another author's packets is needed. -/
theorem ownerPacketFacts_environment {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {bound :
        (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      bound)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
        (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep
        (serviceApplication setup mode deadline leaks) command).support)
    {remaining : Nat}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, command.actor? (serviceApplication setup mode deadline leaks), next⟩))
    (who : Player) (calls : OwnFreshCalls setup leaks bound execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (good : ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message) :
    OwnFreshCalls setup leaks bound next who ∧ FreshCallsConform setup leaks next who ∧
      OneCallPerEvent setup leaks next who ∧
      (∀ message, message.sender = who → Emitted setup leaks next message →
        SettledGood setup leaks next message) := by
  let app := serviceApplication setup mode deadline leaks
  have recallEq := app.environmentStep_recall execution next command reached
  have callsNext : OwnFreshCalls setup leaks bound next who := by
    unfold OwnFreshCalls
    rw [recallEq]
    exact calls
  have conformNext : FreshCallsConform setup leaks next who := by
    unfold FreshCallsConform
    rw [recallEq]
    exact conform
  have onceNext : OneCallPerEvent setup leaks next who := by
    unfold OneCallPerEvent
    rw [recallEq]
    exact once
  refine ⟨callsNext, conformNext, onceNext, ?_⟩
  intro message authored emitted
  have emittedBefore : Emitted setup leaks execution message := by
    unfold Emitted at emitted ⊢
    rw [← app.environmentStep_inputs execution next command reached]
    exact emitted
  exact (good message authored emittedBefore).owner_environment inclusion facts reached trace who
    callsNext conformNext onceNext authored emittedBefore

/-- One physical round preserves the immediate owner's local resources and
the content of every actual packet, independently of all foreign responses. -/
theorem sourceServiceImmediatePolicy_packetFacts_round {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {delay bound :
        (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {who : Player}
    {profile : BehavioralProfile setup.program}
    (follows : players who = serviceImmediatePolicy setup mode deadline leaks bound profile who)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (slots : CanonicalSlotsUsed setup leaks execution who)
    (calls : OwnFreshCalls setup leaks bound execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (good : ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
            execution).support) :
    OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who ∧
      OwnFreshCalls setup leaks bound next who ∧ FreshCallsConform setup leaks next who ∧
      OneCallPerEvent setup leaks next who ∧
      (∀ message, message.sender = who → Emitted setup leaks next message →
        SettledGood setup leaks next message) := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, selected, middle, moved, effect⟩ := round_cases setup leaks reached
  obtain ⟨middleTrace⟩ := app.raw_trace_environment
      (serviceInitialLaw setup mode) horizon scheduler remaining
    execution middle command trace selected moved
  have recallEq := app.environmentStep_recall execution middle command moved
  have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have slotsMiddle := canonicalSlotsUsed_environment moved who slots
  obtain ⟨callsMiddle, conformMiddle, onceMiddle, goodMiddle⟩ := ownerPacketFacts_environment
    contract.inclusion (settledFacts_history
        (serviceInitialLaw setup mode) horizon scheduler trace) moved
      middleTrace who calls conform once good
  rcases effect with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact ⟨atMiddle, slotsMiddle, callsMiddle, conformMiddle, onceMiddle, goodMiddle⟩
  · rw [active] at middleTrace
    by_cases same : responder = who
    · subst responder
      rw [follows] at chosen
      obtain ⟨atNext, slotsNext⟩ := sourceServiceImmediatePolicy_canonicalSlots_respond middleTrace
        atMiddle slotsMiddle chosen
      obtain ⟨callsNext, conformNext, onceNext, goodNext⟩ := ownerPacketFacts_respond middle who
        response (settledFacts_history
            (serviceInitialLaw setup mode) horizon scheduler middleTrace) callsMiddle
        conformMiddle onceMiddle goodMiddle (sourceServiceImmediatePolicy_firstSubmission chosen)
        (sourceServiceImmediatePolicy_freshServiceEnvelope middleTrace atMiddle slotsMiddle chosen)
        (sourceServiceImmediatePolicy_submissionFits chosen)
      exact ⟨atNext, slotsNext, callsNext, conformNext, onceNext, goodNext⟩
    · have different : who ≠ responder := Ne.symm same
      have atNext : OwnSubmissionsAtTurn setup leaks (middle.respond app responder response)
          who := by
        unfold OwnSubmissionsAtTurn
        rw [app.respond_recall_other middle responder who different response]
        exact atMiddle
      have slotsNext := canonicalSlotsUsed_respond_other middle different response slotsMiddle
      obtain ⟨callsNext, conformNext, onceNext, goodNext⟩ := ownerPacketFacts_respond_other middle
        who responder different response
        (settledFacts_history
            (serviceInitialLaw setup mode) horizon scheduler middleTrace) callsMiddle
        conformMiddle onceMiddle goodMiddle
      exact ⟨atNext, slotsNext, callsNext, conformNext, onceNext, goodNext⟩

/-- One actual round preserves the immediate owner's full clear signal and
all local packet resources. Earlier binding turns remain recorded, which
protects newly offered unsent bindings and rules out public omissions. -/
theorem sourceServiceImmediatePolicy_continuationFacts_round {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {delay bound :
        (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {who : Player}
    {profile : BehavioralProfile setup.program}
    (follows : players who = serviceImmediatePolicy setup mode deadline leaks bound profile who)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    (turned : BindingTurnsRecorded setup leaks execution who)
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (slots : CanonicalSlotsUsed setup leaks execution who)
    (calls : OwnFreshCalls setup leaks bound execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (good : ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
            execution).support) :
    ActivationsAnswered setup leaks next ∧ BindingTurnsRecorded setup leaks next who ∧
      (serviceRuntime setup mode deadline).serviceRisk leaks bound who (next.recall who)
        (next.observe (serviceApplication setup mode deadline leaks) who) = false ∧
      OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who ∧
      OwnFreshCalls setup leaks bound next who ∧ FreshCallsConform setup leaks next who ∧
      OneCallPerEvent setup leaks next who ∧
      (∀ message, message.sender = who → Emitted setup leaks next message →
        SettledGood setup leaks next message) := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨atNext, slotsNext, callsNext, conformNext, onceNext, goodNext⟩ :=
    sourceServiceImmediatePolicy_packetFacts_round contract follows trace atTurn slots calls
      conform once good reached
  obtain ⟨nextTrace⟩ := app.raw_trace_round
      (serviceInitialLaw setup mode) horizon scheduler players remaining
    execution next trace reached
  have answeredNext := round_activationsAnswered setup leaks answered reached
  obtain ⟨⟨publicClear, submittedClear⟩, opportunityRecallClear⟩ :=
    ((serviceRuntime setup mode deadline).persistentServiceRisk_clear_iff leaks bound who _ _).mp
      (((serviceRuntime setup mode deadline).serviceRisk_clear_iff leaks bound who _ _).mp clear).1
  obtain ⟨command, selected, middle, moved, effect⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have turnedMiddle : BindingTurnsRecorded setup leaks middle who := by
    unfold BindingTurnsRecorded
    rw [recallEq]
    exact turned
  have recallFacts : BindingTurnsRecorded setup leaks next who ∧
      (serviceRuntime setup mode deadline).recalledSubmissionRisk leaks bound who
          (next.recall who) = false ∧
      (serviceRuntime setup mode deadline).recalledBindingOpportunityRisk leaks bound who
          (next.recall who) =
        false := by
    rcases effect with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
    · refine ⟨turnedMiddle, ?_, ?_⟩ <;> rw [recallEq]
      · exact submittedClear
      · exact opportunityRecallClear
    · by_cases same : responder = who
      · subst responder
        have commandEq : command = .activate who := by
          cases command with
          | activate actor =>
              exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
          | wait | «include» _ | application _ => cases active
        subst commandEq
        have appEq := activation_application setup leaks execution middle who moved
        obtain ⟨middleTrace⟩ := app.raw_trace_environment
            (serviceInitialLaw setup mode) horizon scheduler
          remaining execution middle (.activate who) trace selected moved
        change (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨remaining, some who, middle⟩) at middleTrace
        have middleClear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who
            (middle.recall who)
            (middle.observe app who) = false := by
          have sameRisk := (serviceRuntime setup mode deadline).serviceRisk_congr leaks bound who
            (execution.recall who) (middle.recall who) (execution.observe app who)
            (middle.observe app who) rfl (congrArg EventGraphRuntime.State.publicView appEq.symm)
            (congrArg (fun pastFn => (pastFn who).map
              ((serviceRuntime setup mode deadline).submissionRiskRecord leaks)) recallEq.symm)
          exact sameRisk.symm.trans clear
        have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
          unfold OwnSubmissionsAtTurn
          rw [recallEq]
          exact atTurn
        have slotsMiddle := canonicalSlotsUsed_environment moved who slots
        rw [follows] at chosen
        obtain ⟨turnedAfter, opportunityAfter⟩ := immediatePolicy_recallFacts_respond middleTrace
          atMiddle slotsMiddle turnedMiddle middleClear response chosen
        have submittedAfter :=
          (serviceRuntime setup mode deadline).recalledSubmissionRisk_respond_protected leaks
              bound middle who response
            (sourceServiceImmediatePolicy_submissionFits chosen)
        rw [recallEq] at submittedAfter
        exact ⟨turnedAfter, submittedAfter.trans submittedClear, opportunityAfter⟩
      · have different : who ≠ responder := Ne.symm same
        have otherRecall := app.respond_recall_other middle responder who different response
        refine ⟨?_, ?_, ?_⟩
        · unfold BindingTurnsRecorded
          rw [otherRecall]
          exact turnedMiddle
        · rw [otherRecall, recallEq]
          exact submittedClear
        · rw [otherRecall, recallEq]
          exact opportunityRecallClear
  obtain ⟨turnedNext, submittedNext, opportunityRecallNext⟩ := recallFacts
  have publicNext := recordedBindings_no_public_miss_round contract timely trace answered who
    turned publicClear reached nextTrace callsNext conformNext onceNext atNext
  have persistentNext :=
      ((serviceRuntime setup mode deadline).persistentServiceRisk_clear_iff leaks bound who
    (next.recall who) (next.observe app who)).mpr
      ⟨⟨publicNext, submittedNext⟩, opportunityRecallNext⟩
  have opportunityNext := recordedBindings_currentOpportunity_clear contract timely nextTrace
    answeredNext who turnedNext
  exact ⟨answeredNext, turnedNext,
      (serviceRuntime setup mode deadline).serviceRisk_clear leaks bound who _ _
    persistentNext opportunityNext, atNext, slotsNext, callsNext, conformNext, onceNext, goodNext⟩

/-- A single suffix induction jointly preserves full clear risk, answered
activations, recorded binding turns and the soundness of every owner packet.
Only the selected owner's continuation policy is prescribed. -/
theorem sourceServiceImmediatePolicy_continuationFacts_runRounds {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {delay bound :
        (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (profile : BehavioralProfile setup.program)
    (follows : players who = serviceImmediatePolicy setup mode deadline leaks bound profile who)
    (count : Nat) (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    (turned : BindingTurnsRecorded setup leaks execution who)
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (slots : CanonicalSlotsUsed setup leaks execution who)
    (calls : OwnFreshCalls setup leaks bound execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (good : ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).runRounds scheduler players count
      execution).support) :
    ActivationsAnswered setup leaks next ∧ BindingTurnsRecorded setup leaks next who ∧
      (serviceRuntime setup mode deadline).serviceRisk leaks bound who (next.recall who)
        (next.observe (serviceApplication setup mode deadline leaks) who) = false ∧
      OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who ∧
      OwnFreshCalls setup leaks bound next who ∧ FreshCallsConform setup leaks next who ∧
      OneCallPerEvent setup leaks next who ∧
      (∀ message, message.sender = who → Emitted setup leaks next message →
        SettledGood setup leaks next message) := by
  let app := serviceApplication setup mode deadline leaks
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨answered, turned, clear, atTurn, slots, calls, conform, once, good⟩
  | succ count ih =>
      obtain ⟨middle, moved, finished⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have roundTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨remaining + count + 1, none, execution⟩) := by
        simpa only [Nat.add_assoc] using trace
      obtain ⟨answeredMiddle, turnedMiddle, clearMiddle, atMiddle, slotsMiddle, callsMiddle,
        conformMiddle, onceMiddle, goodMiddle⟩ :=
          sourceServiceImmediatePolicy_continuationFacts_round contract timely follows roundTrace
            answered turned clear atTurn slots calls conform once good moved
      obtain ⟨middleTrace⟩ := app.raw_trace_round
          (serviceInitialLaw setup mode) horizon scheduler players
        (remaining + count) execution middle roundTrace moved
      exact ih middle middleTrace answeredMiddle turnedMiddle clearMiddle atMiddle slotsMiddle
        callsMiddle conformMiddle onceMiddle goodMiddle finished

/-- Every owner packet in actual traffic is permitted by the actual final
record of a clean suffix. This includes packets retained from the prefix. -/
theorem sourceServiceImmediatePolicy_owner_settled_runRounds {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {delay bound :
        (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (profile : BehavioralProfile setup.program)
    (follows : players who = serviceImmediatePolicy setup mode deadline leaks bound profile who)
    (count : Nat) (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    (turned : BindingTurnsRecorded setup leaks execution who)
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (slots : CanonicalSlotsUsed setup leaks execution who)
    (calls : OwnFreshCalls setup leaks bound execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (good : ∀ message, message.sender = who → Emitted setup leaks execution message →
      SettledGood setup leaks execution message)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).runRounds scheduler players count
      execution).support) :
    ∀ record ∈ (serviceApplication setup mode deadline leaks).executionTraffic next,
        record.envelope.sender = who →
      ((serviceRuntime setup mode deadline).settledRecord leaks next).permits record.envelope =
          true := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨_, _, _, _, _, _, _, _, goodNext⟩ :=
    sourceServiceImmediatePolicy_continuationFacts_runRounds contract timely players who profile
      follows count execution next trace answered turned clear atTurn slots calls conform once good
        reached
  obtain ⟨nextTrace⟩ := app.raw_trace_runRounds
      (serviceInitialLaw setup mode) horizon scheduler players
    remaining count execution next trace reached
  have inputs := app.stateTraffic_inputs (serviceInitialLaw setup mode) horizon scheduler nextTrace
  change (app.executionTraffic next).map ReactiveApplication.TrafficRecord.envelope =
    next.network.inputs at inputs
  intro record member authored
  have emitted : Emitted setup leaks next record.envelope := by
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  exact (goodNext record.envelope authored emitted).permits

section Prefix

variable [Fintype Player]

/-- A legal clear active risk-menu prefix supplies all packet premises after
one actual immediate response. Earlier silent turns are retained in recall. -/
theorem sourceServiceImmediatePolicy_packetFacts_after_prefix_response
    (bounds : MessageBounds (serviceGraph setup mode)) {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {delay bound :
        (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (who : Player) (profile : BehavioralProfile setup.program)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      (execution.recall who) (execution.observe
          (serviceApplication setup mode deadline leaks) who)).support) :
    OwnSubmissionsAtTurn setup leaks (execution.respond
        (serviceApplication setup mode deadline leaks) who response)
        who ∧
      CanonicalSlotsUsed setup leaks (execution.respond
          (serviceApplication setup mode deadline leaks) who response)
        who ∧
      OwnFreshCalls setup leaks bound (execution.respond
          (serviceApplication setup mode deadline leaks) who response)
        who ∧
      FreshCallsConform setup leaks (execution.respond
          (serviceApplication setup mode deadline leaks) who response)
        who ∧
      OneCallPerEvent setup leaks (execution.respond
          (serviceApplication setup mode deadline leaks) who response) who ∧
      (∀ message, message.sender = who →
        Emitted setup leaks (execution.respond
            (serviceApplication setup mode deadline leaks) who response) message →
        SettledGood setup leaks (execution.respond
            (serviceApplication setup mode deadline leaks) who response)
          message) := by
  let menu := bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound
  have persistent :=
      ((serviceRuntime setup mode deadline).serviceRisk_clear_iff leaks bound who _ _).mp clear |>.1
  obtain ⟨atTurn, slots⟩ := riskCanonicalSlots_history bounds bound _ trace who persistent
  obtain ⟨calls, conform, once, good⟩ := riskPacketFacts_history bounds bound contract _ trace who
    persistent
  have rawTrace := menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler trace
  obtain ⟨atNext, slotsNext⟩ := sourceServiceImmediatePolicy_canonicalSlots_respond rawTrace atTurn
    slots chosen
  obtain ⟨callsNext, conformNext, onceNext, goodNext⟩ := ownerPacketFacts_respond execution who
    response (settledFacts_history
        (serviceInitialLaw setup mode) horizon scheduler rawTrace) calls conform once
    good (sourceServiceImmediatePolicy_firstSubmission chosen)
    (sourceServiceImmediatePolicy_freshServiceEnvelope rawTrace atTurn slots chosen)
    (sourceServiceImmediatePolicy_submissionFits chosen)
  exact ⟨atNext, slotsNext, callsNext, conformNext, onceNext, goodNext⟩

end Prefix

end Vegas
