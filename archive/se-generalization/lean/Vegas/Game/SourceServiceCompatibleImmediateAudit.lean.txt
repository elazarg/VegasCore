/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceSourceSites
import Vegas.Game.SourceServiceImmediateAudit
import Vegas.Pending.ReactiveBindingRiskRecall

/-! # A clean immediate continuation from compatible RAW information

The source-compatible witness supplies actual owner packet and slot facts to
every initialized RAW history with the same full owner input. Public readiness,
completion, receipts and settled content agree; authentic own recall identifies
the same emitted envelopes. Foreign prefix and suffix responses remain RAW.

The existing physical continuation induction then gives zero owner collection
after the immediate owner's first response. No original risk-menu trace or
future owner menu-support premise is imposed on the actual RAW continuation.
This does not assert a source continuation law or utility comparison.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability
  GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [Fintype Player] in
private theorem completed_iff_of_public_eq
    (left right : (application setup leaks).Execution)
    (same : left.application.publicView = right.application.publicView)
    (event : (graph setup).EventId) :
    event ∈ left.application.config.cut.completed ↔
      event ∈ right.application.config.cut.completed := by
  rw [← left.application.config.history_exact event, ← right.application.config.history_exact event]
  change event ∈ left.application.publicView.observation.completionOrder ↔
    event ∈ right.application.publicView.observation.completionOrder
  rw [same]

omit [Fintype Player] in
private theorem settledGood_of_input_eq
    (left right : (application setup leaks).Execution)
    (publicEq : left.application.publicView = right.application.publicView)
    (receiptsEq : left.receipts = right.receipts)
    (message : Message Player (WitnessedPacket (graph setup)))
    (good : SettledGood setup leaks left message) : SettledGood setup leaks right message := by
  obtain ⟨event, named, status⟩ := good
  refine ⟨event, named, ?_⟩
  rcases status with pending | accepted
  · left
    refine ⟨?_, ?_, ?_⟩
    · apply (right.application.publicView_eventReady event).mp
      rw [← publicEq]
      exact (left.application.publicView_eventReady event).mpr pending.1
    · rw [← receiptsEq]
      exact pending.2.1
    · have content := pending.2.2
      cases packet : message.payload.call <;> simp only [PendingContent, packet] at content ⊢
      all_goals first | exact content | rwa [← publicEq]
  · right
    refine ⟨receiptsEq ▸ accepted.1,
      (completed_iff_of_public_eq left right publicEq event).mp accepted.2.1, ?_⟩
    have sameRecord : (runtime setup).settledRecord leaks left =
        (runtime setup).settledRecord leaks right := by
      unfold EventGraphRuntime.settledRecord
      rw [publicEq, receiptsEq]
    rw [← sameRecord]
    exact accepted.2.2

end Vegas

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability
  GameTheory.Enforcement GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "runtime" => runtime service.setup
local notation "menu" => service.bounds.riskMenu (runtime) service.leaks service.bound

/-- The actual initialized RAW prefix obtains every owner resource from its
compatible information witness. These facts are derived, rather than required
of the caller or of the foreign prefix policies. -/
theorem sourceCompatibleInfo_raw_prefixFacts
    (control : (app).Control)
    (trace : ((app).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some control)) (who : Player)
    (compatible : service.sourceCompatibleInfo who
      (some (control.execution.recall who, control.execution.observe (app) who))) :
    (runtime).serviceRisk service.leaks service.bound who (control.execution.recall who)
        (control.execution.observe (app) who) = false ∧
      OwnSubmissionsAtTurn service.setup service.leaks control.execution who ∧
      CanonicalSlotsUsed service.setup service.leaks control.execution who ∧
      OwnFreshCalls service.setup service.leaks service.bound control.execution who ∧
      FreshCallsConform service.setup service.leaks control.execution who ∧
      OneCallPerEvent service.setup service.leaks control.execution who ∧
      ∀ message, message.sender = who → Emitted service.setup service.leaks control.execution
        message → SettledGood service.setup service.leaks control.execution message := by
  obtain ⟨_profile, _turns, _timing, _permitted, _effective, history, remaining, witness,
    current, observed, _supported, allClear, clear⟩ := compatible
  have witnessTrace : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).Trace (some ⟨remaining, some who, witness⟩) := current ▸ history.trace
  have input : (witness.recall who, witness.observe (app) who) =
      (control.execution.recall who, control.execution.observe (app) who) := by
    apply Option.some.inj
    have atState : ((menu).information (initialLaw service.setup) service.horizon
        service.scheduler).infoOf who history.trace = (app).observe who history.state :=
      (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
    rw [atState, current] at observed
    simpa only [ReactiveApplication.observe, ↓reduceIte] using observed
  have recalled : witness.recall who = control.execution.recall who := congrArg Prod.fst input
  have viewed : witness.observe (app) who = control.execution.observe (app) who :=
    congrArg Prod.snd input
  have publicEq : witness.application.publicView = control.execution.application.publicView :=
    congrArg (fun view : (app).PlayerView => view.application.publicView) viewed
  have receiptsEq : witness.receipts = control.execution.receipts :=
    congrArg ReactiveApplication.PlayerView.receipts viewed
  obtain ⟨atTurn, slots⟩ := riskCanonicalSlots_history service.bounds service.bound _ witnessTrace
    who (allClear who)
  obtain ⟨calls, conform, once, good⟩ := riskPacketFacts_history service.bounds service.bound
    service.contract _ witnessTrace who (allClear who)
  have witnessRaw := (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    witnessTrace
  have witnessFacts := legalFacts service.setup service.leaks service.horizon service.scheduler
    ⟨remaining, some who, witness⟩ witnessRaw
  have actualFacts := legalFacts service.setup service.leaks service.horizon service.scheduler
    control trace
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [← recalled, ← viewed]
  · unfold OwnSubmissionsAtTurn at atTurn ⊢
    rwa [← recalled]
  · intro serial member
    rw [← recalled] at member
    rcases slots serial member with lower | ⟨equal, event, payload, layout, unfinished, recorded⟩
    · exact Or.inl (publicEq ▸ lower)
    · refine Or.inr ⟨publicEq ▸ equal, event, payload, layout, ?_, ?_⟩
      · exact fun finished => unfinished
          ((completed_iff_of_public_eq witness control.execution publicEq event).mpr finished)
      · rwa [← recalled]
  · unfold OwnFreshCalls at calls ⊢
    rwa [← recalled]
  · unfold FreshCallsConform at conform ⊢
    rwa [← recalled]
  · unfold OneCallPerEvent at once ⊢
    rwa [← recalled]
  · intro message authored emitted
    have owned : message ∈ control.execution.network.inputs.filter
        (fun item => item.sender = who) :=
      List.mem_filter.mpr ⟨emitted, by simpa only [decide_eq_true_eq] using authored⟩
    rw [actualFacts.inputs who, ← recalled, ← witnessFacts.inputs who] at owned
    exact settledGood_of_input_eq witness control.execution publicEq receiptsEq message
      (good message authored (List.mem_filter.mp owned).1)

/-- Arbitrary foreign RAW continuations preserve the owner's clear signal and
the good settled content of all of its traffic, including the actual prefix.
The suffix uses the existing physical induction after one immediate response. -/
theorem sourceCompatibleInfo_immediate_clean_continuation
    {remaining : Nat} (execution : (app).Execution) (who : Player)
    (trace : ((app).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (players : Player → (app).Policy) (profile : BehavioralProfile service.setup.program)
    (follows : players who = sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who)
    (response : (app).Action)
    (chosen : response ∈ (sourceServiceImmediatePolicy service.setup service.leaks service.bound
      profile who (execution.recall who) (execution.observe (app) who)).support)
    (count : Nat) (within : count ≤ remaining) (next : (app).Execution)
    (reached : next ∈ ((app).runRounds service.scheduler players count
      (execution.respond (app) who response)).support) :
    (runtime).serviceRisk service.leaks service.bound who (next.recall who)
        (next.observe (app) who) = false ∧
      next.application.publicView.missedDecisionBy who = false ∧
      (∀ record ∈ (app).executionTraffic next, record.envelope.sender = who →
        ((runtime).settledRecord service.leaks next).permits record.envelope = true) := by
  let start := execution.respond (app) who response
  obtain ⟨clear, atTurn, slots, calls, conform, once, good⟩ :=
    service.sourceCompatibleInfo_raw_prefixFacts ⟨remaining, some who, execution⟩ trace who
      compatible
  have components := ((runtime).serviceRisk_clear_iff service.leaks service.bound who _ _).mp clear
  have turned := sourceServiceImmediatePolicy_ownTurnsRecorded_respond trace atTurn slots clear
    response chosen
  obtain ⟨traceStart⟩ := (app).raw_trace_respond (initialLaw service.setup) service.horizon
    service.scheduler remaining execution who response trace
  have answered : ActivationsAnswered service.setup service.leaks start :=
    (runtime).activations_answered_history service.leaks (initialLaw service.setup) service.horizon
      service.scheduler start remaining traceStart
  have persistentClear : (runtime).persistentServiceRisk service.leaks service.bound who
      (start.recall who) (start.observe (app) who) = false :=
    ((runtime).persistentServiceRisk_respond_protected service.leaks service.bound execution who
      response (sourceServiceImmediatePolicy_submissionFits chosen) components.2).trans components.1
  have clearStart := (runtime).serviceRisk_clear service.leaks service.bound who (start.recall who)
    (start.observe (app) who) persistentClear
    (recordedTurns_currentOpportunity_clear service.contract service.timely traceStart answered
      who turned)
  obtain ⟨atStart, slotsStart⟩ := sourceServiceImmediatePolicy_canonicalSlots_respond trace atTurn
    slots chosen
  obtain ⟨callsStart, conformStart, onceStart, goodStart⟩ := ownerPacketFacts_respond execution who
    response (settledFacts_history (initialLaw service.setup) service.horizon service.scheduler
      trace) calls conform once good (sourceServiceImmediatePolicy_firstSubmission chosen)
    (sourceServiceImmediatePolicy_freshServiceEnvelope trace atTurn slots chosen)
    (sourceServiceImmediatePolicy_submissionFits chosen)
  have traceBudget : ((app).protocol (initialLaw service.setup) service.horizon
      service.scheduler).Trace (some ⟨(remaining - count) + count, none, start⟩) := by
    simpa only [Nat.sub_add_cancel within] using traceStart
  obtain ⟨_, _, clearNext, _, _, _, _, _, goodNext⟩ :=
    sourceServiceImmediatePolicy_continuationFacts_runRounds service.contract service.timely players
      who profile follows count start next traceBudget answered turned clearStart atStart slotsStart
        callsStart conformStart onceStart goodStart reached
  have noMiss := ((runtime).persistentServiceRisk_clear_iff service.leaks service.bound who _ _).mp
    (((runtime).serviceRisk_clear_iff service.leaks service.bound who _ _).mp clearNext).1 |>.1.1
  refine ⟨clearNext, noMiss, ?_⟩
  obtain ⟨nextTrace⟩ := (app).raw_trace_runRounds (initialLaw service.setup) service.horizon
    service.scheduler players (remaining - count) count start next traceBudget reached
  have inputs := (app).stateTraffic_inputs (initialLaw service.setup) service.horizon
    service.scheduler nextTrace
  change ((app).executionTraffic next).map ReactiveApplication.TrafficRecord.envelope =
    next.network.inputs at inputs
  intro record member authored
  have emitted : Emitted service.setup service.leaks next record.envelope := by
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  exact (goodNext record.envelope authored emitted).permits

/-- Authentic sampling collects zero owner charge on the real immediate
continuation from compatible RAW information. Observation may remain partial
and correlated, and no foreign response menu is required. -/
theorem sourceCompatibleInfo_immediate_audit_clear_after_response
    {remaining : Nat} (execution : (app).Execution) (who : Player)
    (trace : ((app).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (players : Player → (app).Policy) (profile : BehavioralProfile service.setup.program)
    (follows : players who = sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who)
    (response : (app).Action)
    (chosen : response ∈ (sourceServiceImmediatePolicy service.setup service.leaks service.bound
      profile who (execution.recall who) (execution.observe (app) who)).support)
    (count : Nat) (within : count ≤ remaining) (next : (app).Execution)
    (reached : next ∈ ((app).runRounds service.scheduler players count
      (execution.respond (app) who response)).support)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample)
        (some ⟨remaining - count, none, next⟩) who = 0 := by
  obtain ⟨_, noMiss, permits⟩ := service.sourceCompatibleInfo_immediate_clean_continuation execution
    who trace compatible players profile follows response chosen count within next reached
  unfold sourceServiceAudit
  rw [(runtime).serviceAudit_charge, noMiss]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply (app).sampledTrafficAudit_sound
  · exact authentic _
  · exact permits

/-- The one physical immediate-owner comparator has zero actual terminal
collection from compatible RAW information against arbitrary foreign RAW
policies. The remaining fuel is the actual initialized control's budget. -/
theorem sourceCompatibleInfo_immediate_finish_charge_zero
    {remaining : Nat} (execution : (app).Execution) (who : Player)
    (trace : ((app).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (foreign : Player → (app).Policy) (profile : BehavioralProfile service.setup.program)
    (final : (app).ProtocolState)
    (reached : final ∈ ((app).finish (initialLaw service.setup) service.horizon service.scheduler
      (Function.update foreign who (sourceServiceImmediatePolicy service.setup service.leaks
        service.bound profile who)) (some ⟨remaining, some who, execution⟩)).support)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) final who = 0 := by
  let players := Function.update foreign who
    (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who)
  have followed : players who = sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who := Function.update_self ..
  change final ∈ ((app).finish (initialLaw service.setup) service.horizon service.scheduler players
    (some ⟨remaining, some who, execution⟩)).support at reached
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, ReactiveApplication.invoke,
    PMF.bind_map] at reached
  obtain ⟨next, continued, stateEq⟩ := PMF.support_map .. ▸ reached
  obtain ⟨response, chosen, nextReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ continued)
  rw [followed] at chosen
  have zero := service.sourceCompatibleInfo_immediate_audit_clear_after_response execution who
    trace compatible players profile followed response chosen remaining le_rfl next nextReached
      sample authentic
  rw [← stateEq]
  simpa only [Nat.sub_self, ReactiveApplication.finished] using zero

end Vegas.AsyncServiceSpec
