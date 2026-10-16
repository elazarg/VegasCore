/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingServiceTapeOrder
import Interaction.ReactiveProvenance

/-! # Complete counted binding episodes under original local service tapes -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => onePacketMenu runtime leaks bounds

include ordered in
/-- A coordinate packet retained after an entire binding episode recovers its
actual unsent callback and the same immutable tape's supported SEND. No
receipt, matching ordinal or desired declaration-shape premise is supplied. -/
theorem bindingServiceTapeMember_emission_origin
    (outside : (app).Policy)
    (owner : Player) (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (tape : Fin horizon → Bool × Bool) (remaining : Nat) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (consistent : (bindingServiceTapeMember runtime leaks bounds outside owner coordinate
      payload values
      choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent (execution.recall owner))
    (message : Message Player (CommitAttemptPacket graph))
    (authored : message ∈ (app).outputs (execution.recall owner))
    (named : event? message.payload = some coordinate) :
    ∃ (before : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
      (action : (app).Action),
      TracePrefix prior trace ∧ before.actor = some owner ∧
      before.execution.application.SeedRequest owner coordinate ∧
      (∀ packet ∈ (app).outputs (before.execution.recall owner),
        event? packet.payload ≠ some coordinate) ∧
      (bindingServiceTapeMember runtime leaks bounds outside owner coordinate payload values choose
        failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
          slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tape).Consistent
            (before.execution.recall owner) ∧
      action ∈ (bindingServiceTapeMember runtime leaks bounds outside owner coordinate payload
        values
        choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
          slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tape
            (before.execution.recall owner) (before.execution.observe app owner)).support ∧
      action.transmission.isSome = true ∧
      ((PhaseSeedScheduler.informationInput runtime leaks coordinate owner
        (before.execution.recall owner) (before.execution.observe app owner)).elapsed, message) ∈
        (PhaseSeedScheduler.localInput runtime leaks coordinate owner execution.environmentRecall
          (execution.observeEnvironment app)).emissions := by
  classical
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have recalled := (app).history_inputRecall initial horizon scheduler raw
  have own : message.sender = owner := by
    rw [← recalled owner] at authored
    exact of_decide_eq_true (List.mem_filter.mp authored).2
  have input : message ∈ execution.network.inputs := by
    rw [← recalled owner] at authored
    exact (List.mem_filter.mp authored).1
  obtain ⟨entry, retained, material, transmitted, emitted, _state, _known, _packet⟩ :=
    ((app).history_provenance initial horizon scheduler raw).inputs message input
  rw [own] at retained
  obtain ⟨before, prior, isPrefix, active, viewed, supported, suffix, pastEq⟩ :=
    (menu).recorded_response_supported initial horizon scheduler ⟨remaining, none, execution⟩
      trace owner (bindingServiceTapeMember runtime leaks bounds outside owner coordinate
        payload values
        choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
          slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tape)
            consistent entry retained
  have priorRaw := (menu).toRawTrace initial horizon scheduler prior
  have beforeActive : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨before.remaining, some owner, before.execution⟩) := by
    simpa only [← active] using prior
  obtain ⟨_legalBefore, _legalPrior, _legalPrefix, _legalActive, _legalPast, legalView, offered⟩ :=
    (menu).recorded_response_at initial horizon scheduler ⟨remaining, none, execution⟩ trace owner
      (before.execution.recall owner) entry suffix pastEq
  rw [← legalView, viewed] at offered
  have actionEq : entry.action = ⟨some material⟩ := by
    cases actionAt : entry.action with
    | mk transmission =>
        simpa only [actionAt] using congrArg ReactiveApplication.Action.mk transmitted
  have offeredSend := actionEq ▸ offered
  obtain ⟨actual, actualRequest⟩ := onePacket_request_of_nonsilent runtime leaks bounds plan inputs
    horizon scheduler before.remaining owner before.execution beforeActive material offeredSend
  have actualNamed := onePacket_event_of_request runtime leaks bounds plan ordered inputs horizon
    scheduler before.remaining owner before.execution beforeActive actual actualRequest material
      offeredSend
  have fields : message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event := by
    unfold event? at named
    obtain ⟨event, eventEq, same⟩ := Option.map_eq_some_iff.mp named
    cases same
    exact ⟨rfl, eventEq⟩
  have exactCall := phase_emit_call _state message.sender _known material
  change _state.emit message.sender _known material = message.payload at _packet
  have callEq : material.call.packet = message.payload.packet.call :=
    exactCall.symm.trans (congrArg (fun packet => packet.packet.call) _packet)
  have actualTag := phase_recalled_emission_attempt runtime leaks initial horizon scheduler raw
    owner entry retained message emitted
  rw [viewed] at actualTag
  have tagEq : actual.attempt = coordinate.attempt :=
    actualRequest.1.trans (actualTag.symm.trans fields.1)
  have eventEq : actual.event = coordinate.event := Option.some.inj
    (actualNamed.symm.trans ((congrArg (Payload.event? graph) callEq).trans fields.2))
  have sameCoordinate : actual = coordinate := by
    cases actual with
    | mk actualTag actualEvent =>
        cases coordinate with
        | mk expectedTag expectedEvent =>
            change actualTag = expectedTag at tagEq
            change actualEvent = expectedEvent at eventEq
            cases tagEq
            cases eventEq
            rfl
  have request : before.execution.application.SeedRequest owner coordinate :=
    sameCoordinate ▸ actualRequest
  obtain ⟨inputState, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler priorRaw
  have requested := (PhaseRuntimeState.requests_publicView _ valid owner coordinate).mpr request
  change PhaseRuntimeState.requests
    (before.execution.observe app owner).application.2 owner coordinate at requested
  have unsent := unsent_of_nonsilent runtime leaks bounds plan ordered inputs horizon scheduler
    before.remaining owner before.execution beforeActive coordinate request material
      (actionEq ▸ offered)
  have beforeConsistent : (bindingServiceTapeMember runtime leaks bounds outside owner
    coordinate payload
      values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent (before.execution.recall owner) := by
    rw [pastEq] at consistent
    exact ReactiveApplication.Policy.Consistent.of_append consistent
  refine ⟨before, prior, entry.action, isPrefix, active, request, unsent, beforeConsistent,
    supported, by simp only [transmitted, Option.isSome_some], ?_⟩
  have packetSelected : PhaseSeedScheduler.ownPacket coordinate owner message = true := by
    simp only [PhaseSeedScheduler.ownPacket, decide_eq_true_eq]
    exact ⟨own, fields⟩
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks menu initial horizon
    scheduler remaining execution trace
  rw [PhaseSeedScheduler.localInput_word, words owner coordinate]
  apply List.mem_flatMap.mpr
  let record : Nat × List (Message Player (CommitAttemptPacket graph)) :=
    (entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt coordinate.event).getD
        entry.beforeView.application.2.native.clock,
      entry.emitted.toList.filter (PhaseSeedScheduler.ownPacket coordinate owner))
  refine ⟨record, ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨entry, List.mem_filter.mpr ⟨retained, by
      simpa only [viewed, decide_eq_true_eq] using requested⟩, rfl⟩
  · apply List.mem_map.mpr
    refine ⟨message, List.mem_filter.mpr ⟨Option.mem_toList.mpr emitted, packetSelected⟩, ?_⟩
    simp only [record, PhaseSeedScheduler.informationInput, viewed]


include ordered in
/-- Entire genuine binding episodes have the same resolved success under one
original event seed and one original local timing tape. Private source laws,
packet preparations, handles, nonces and foreign interleavings may differ.
First-SEND ordinals and never-SEND exhaustion are derived from actual recall. -/
theorem bindingServiceTapeMember_accepted_iff_of_resolved
    (outside : (app).Policy)
    {LocalSeed RestSeed : Type}
    (seedLaw : PMF (RestSeed × (PhaseSeedAddress graph → LocalSeed)))
    (family : (RestSeed × (PhaseSeedAddress graph → LocalSeed)) → (app).Scheduler)
    (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs horizon
      seedLaw family)
    (privateSuccess : PhaseService.PrivateBindingSuccess runtime leaks bounds plan inputs horizon
      seedLaw family)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (firstValues secondValues : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (capacity : horizon ≤ bounds.candidateCount) (tape : Fin horizon → Bool × Bool)
    (firstRemaining secondRemaining : Nat) (first second : (app).Execution)
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨firstRemaining, none, first⟩))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨secondRemaining, none, second⟩))
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (firstReady : ∃ (before : (app).Control)
      (beforeTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace (some before)),
      TracePrefix beforeTrace firstTrace ∧
        before.execution.application.SeedRequest owner coordinate.1)
    (secondReady : ∃ (before : (app).Control)
      (beforeTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace (some before)),
      TracePrefix beforeTrace secondTrace ∧
        before.execution.application.SeedRequest owner coordinate.1)
    (firstResolved : coordinate.1.Resolved first.application)
    (secondResolved : coordinate.1.Resolved second.application)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (firstConsistent : (bindingServiceTapeMember runtime leaks bounds outside owner coordinate.1
      payload
      firstValues choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent (first.recall owner))
    (secondConsistent : (bindingServiceTapeMember runtime leaks bounds outside owner
      coordinate.1 payload
      secondValues choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent (second.recall owner)) :
    PhaseService.BindingAccepted runtime leaks coordinate.1 owner first ↔
      PhaseService.BindingAccepted runtime leaks coordinate.1 owner second := by
  classical
  by_cases firstSent : ∃ message ∈ (app).outputs (first.recall owner),
      event? message.payload = some coordinate.1
  · obtain ⟨firstMessage, firstOutput, firstNamed⟩ := firstSent
    obtain ⟨beforeFirst, priorFirst, firstAction, _firstPrefix, firstActive, firstRequest,
      firstUnsent, firstPast, firstChosen, firstSends, firstEmission⟩ :=
      bindingServiceTapeMember_emission_origin (outside := outside) runtime leaks bounds plan
        ordered inputs horizon
        (family firstSeeds) owner coordinate.1 payload firstValues choose failure timing
          firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
            slotBounded rawWeight rawNonnegative rawBounded tape firstRemaining first firstTrace
              firstConsistent firstMessage firstOutput firstNamed
    by_cases secondSent : ∃ message ∈ (app).outputs (second.recall owner),
        event? message.payload = some coordinate.1
    · obtain ⟨secondMessage, secondOutput, secondNamed⟩ := secondSent
      obtain ⟨beforeSecond, priorSecond, secondAction, _secondPrefix, secondActive, secondRequest,
        secondUnsent, secondPast, secondChosen, secondSends, secondEmission⟩ :=
        bindingServiceTapeMember_emission_origin (outside := outside) runtime leaks bounds plan
          ordered inputs horizon
          (family secondSeeds) owner coordinate.1 payload secondValues choose failure timing
            firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
              slotNonnegative slotBounded rawWeight rawNonnegative rawBounded tape secondRemaining
                second secondTrace secondConsistent secondMessage secondOutput secondNamed
      have sameIndex := bindingServiceTapeMember_send_index_eq (outside := outside) runtime
        leaks bounds plan ordered
        inputs horizon seedLaw family calendar firstSeeds secondSeeds firstSupport secondSupport
          owner coordinate payload firstValues secondValues choose failure timing firstNonnegative
            firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
              rawWeight rawNonnegative rawBounded capacity tape beforeFirst beforeSecond priorFirst
                priorSecond firstActive secondActive output firstRequest secondRequest sameSeed
                  firstUnsent secondUnsent catalogue firstPast secondPast firstAction secondAction
                    firstChosen secondChosen firstSends secondSends
      have firstActiveTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
          (some ⟨beforeFirst.remaining, some owner, beforeFirst.execution⟩) := by
        simpa only [← firstActive] using priorFirst
      have secondActiveTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
          (some ⟨beforeSecond.remaining, some owner, beforeSecond.execution⟩) := by
        simpa only [← secondActive] using priorSecond
      exact PhaseService.PrivateActivationCalendar.accepted_iff_of_callbacks runtime leaks bounds
        plan inputs horizon seedLaw family calendar privateSuccess firstSeeds firstSupport
          secondSeeds secondSupport beforeFirst.remaining beforeSecond.remaining firstRemaining
            secondRemaining owner beforeFirst.execution beforeSecond.execution first second
              firstActiveTrace secondActiveTrace firstTrace secondTrace coordinate payload output
                firstRequest secondRequest sameSeed sameIndex firstUnsent secondUnsent firstResolved
                  secondResolved firstMessage secondMessage firstEmission secondEmission
    · have secondUnsent : ∀ message ∈ (app).outputs (second.recall owner),
          event? message.payload ≠ some coordinate.1 := by
        intro message found named
        exact secondSent ⟨message, found, named⟩
      have silent := bindingServiceTapeMember_silent_of_resolved_unsent (outside := outside)
        runtime leaks bounds plan
        ordered inputs horizon seedLaw family calendar firstSeeds secondSeeds firstSupport
          secondSupport owner coordinate payload firstValues secondValues choose failure timing
            firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
              slotNonnegative slotBounded rawWeight rawNonnegative rawBounded capacity tape
                beforeFirst secondRemaining second priorFirst secondTrace firstActive output
                  firstRequest secondReady secondResolved sameSeed firstUnsent secondUnsent
                    catalogue secondConsistent firstAction firstChosen
      rw [silent, Option.isSome_none] at firstSends
      cases firstSends
  · have firstUnsent : ∀ message ∈ (app).outputs (first.recall owner),
        event? message.payload ≠ some coordinate.1 := by
      intro message found named
      exact firstSent ⟨message, found, named⟩
    by_cases secondSent : ∃ message ∈ (app).outputs (second.recall owner),
        event? message.payload = some coordinate.1
    · obtain ⟨secondMessage, secondOutput, secondNamed⟩ := secondSent
      obtain ⟨beforeSecond, priorSecond, secondAction, _secondPrefix, secondActive, secondRequest,
        secondUnsent, _secondPast, secondChosen, secondSends, _secondEmission⟩ :=
        bindingServiceTapeMember_emission_origin (outside := outside) runtime leaks bounds plan
          ordered inputs horizon
          (family secondSeeds) owner coordinate.1 payload secondValues choose failure timing
            firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
              slotNonnegative slotBounded rawWeight rawNonnegative rawBounded tape secondRemaining
                second secondTrace secondConsistent secondMessage secondOutput secondNamed
      have silent := bindingServiceTapeMember_silent_of_resolved_unsent (outside := outside)
        runtime leaks bounds plan
        ordered inputs horizon seedLaw family calendar secondSeeds firstSeeds secondSupport
          firstSupport owner coordinate payload secondValues firstValues choose failure timing
            firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
              slotNonnegative slotBounded rawWeight rawNonnegative rawBounded capacity tape
                beforeSecond firstRemaining first priorSecond firstTrace secondActive output
                  secondRequest firstReady firstResolved sameSeed.symm secondUnsent firstUnsent
                    catalogue firstConsistent secondAction secondChosen
      rw [silent, Option.isSome_none] at secondSends
      cases secondSends
    · have secondUnsent : ∀ message ∈ (app).outputs (second.recall owner),
          event? message.payload ≠ some coordinate.1 := by
        intro message found named
        exact secondSent ⟨message, found, named⟩
      have impossible (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
          (remaining : Nat) (execution : (app).Execution)
          (trace : ((menu).protocol initial horizon (family seeds)).Trace
            (some ⟨remaining, none, execution⟩))
          (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
            event? message.payload ≠ some coordinate.1) :
          ¬ PhaseService.BindingAccepted runtime leaks coordinate.1 owner execution := by
        rintro ⟨message, input, sender, attempt, event, _receipt⟩
        have recalled := (app).history_inputRecall initial horizon (family seeds)
          ((menu).toRawTrace initial horizon (family seeds) trace)
        have authored : message ∈ (app).outputs (execution.recall owner) := by
          rw [← recalled owner]
          exact List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
        apply unsent message authored
        simp only [event?, event, Option.map_some, attempt]
      exact iff_of_false (impossible firstSeeds firstRemaining first firstTrace firstUnsent)
        (impossible secondSeeds secondRemaining second secondTrace secondUnsent)

end Vegas.EventGraphRuntime.PhaseCount
