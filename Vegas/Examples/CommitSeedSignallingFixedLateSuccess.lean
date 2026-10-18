/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingInitialPollRequests
import Vegas.Examples.CommitSeedSignallingProperBinding
import Vegas.Examples.CommitSeedSignallingProperOpening
import Vegas.Examples.CommitSeedSignallingOriginalLateAdmission
import Vegas.Pending.PhaseReadyResolution
import Vegas.Pending.PhaseBindingAcceptedReceipt
import Interaction.ReactiveAllocation
import Interaction.ReactiveAnchoredSupport

/-! # The actual proper packet at the first late inclusion opportunity -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

section Counted

variable (profile : ∀ who, countedModel.BehavioralPolicy who)

local notation "players" => countedMenu.decodeProfile initial horizon scheduler profile

/-- On the correct original seed the actual first late callback chooses a
fresh TRUE packet, without any assumption about an opponent's future values. -/
theorem fixed_late_first_packet (seed : Seeds) (owner : Player)
    (correct : seedBits seed owner = false)
    (ownerPolicy : players owner = fixedLatePolicy owner)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players (firstLatePosition owner)
      initialExecution).support) :
    let observed := completeActivation execution owner
    ∃ serial, serial < horizon ∧
      players owner (observed.recall owner) (observed.observe app owner) =
        PMF.pure (phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
          (.success true) serial) ∧
      reactiveFreshSlot (observed.observe app owner).application.1 = some serial ∧
      observed.application.current.native.candidates.lookup (owner, .prepared serial) = .fresh ∧
      (let next := observed.respond app owner
        (phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
          (.success true) serial);
       next.application.current.native.bindingResult (owner, .prepared serial) .bool) =
        .success true := by
  classical
  obtain ⟨request, recalled⟩ := original_first_poll_request_recall profile seed owner
    aliceWait bobWait execution reached
  have original : execution.application.attempt = originalAttempt := request.1.symm
  obtain ⟨prior⟩ := counted_profile_trace profile seed (firstLatePosition owner)
    (by fin_cases owner <;> decide) execution reached
  have prior : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - firstLatePosition owner - 1 + 1, none, execution⟩) := by
      convert prior using 1; fin_cases owner <;> rfl
  have valid := raw_native_valid (family seed)
    ⟨horizon - firstLatePosition owner - 1 + 1, none, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) prior)
  have length := app.runRounds_environmentRecall_length (family seed) players
    (firstLatePosition owner) initialExecution
    execution reached
  have countEq : execution.environmentRecall.length = firstLatePosition owner := by
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using length
  have readyEq : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true := by
    change decide (PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, (bindingEvent owner)⟩) = true
    apply decide_eq_true
    apply (execution.application.requests_publicView valid owner _).mpr
    simpa only [originalCoordinate, original] using request
  have command : family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.activate owner) := by
    rw [family_first_late_command seed owner _ _ original countEq]
    simp only [correct, pollCommand, ite_true, activateReady, readyEq]
  have moved : completeActivation execution owner ∈
      (execution.environmentStep app (.activate owner)).support := by
    rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨pending⟩ := countedMenu.trace_environment initial horizon (family seed)
    (horizon - firstLatePosition owner - 1) execution
    (completeActivation execution owner) (.activate owner) prior
    (by rw [command]; exact (PMF.mem_support_pure_iff _ _).mpr rfl) moved
  have nativeTrace := countedMenu.toRawTrace initial horizon (family seed) prior
  have clock := original_clock_index seed
    ⟨horizon - firstLatePosition owner - 1 + 1, none, execution⟩ nativeTrace original
  rw [countEq] at clock
  have clockLate : execution.application.current.native.clock = lateClock owner false := by
    fin_cases owner <;> exact clock
  have timer := original_timer (family seed)
    ⟨horizon - firstLatePosition owner - 1 + 1, none, execution⟩ nativeTrace original
    (bindingEvent owner) (by
      fin_cases owner
      · exact Or.inl rfl
      · exact Or.inr rfl) request.2.2.1.1
  have observedRequest : (completeActivation execution owner).application.SeedRequest owner
      ⟨(completeActivation execution owner).application.attempt, (bindingEvent owner)⟩ := by
    change execution.application.SeedRequest owner
      ⟨execution.application.attempt, (bindingEvent owner)⟩
    simpa only [originalCoordinate, original] using request
  have unsent : ∀ message ∈ app.outputs ((completeActivation execution owner).recall owner),
      PhaseCount.event? message.payload ≠
        some ⟨(completeActivation execution owner).application.attempt, (bindingEvent owner)⟩ := by
    change ∀ message ∈ app.outputs (execution.recall owner), _
    rw [recalled]
    have empty : app.outputs (quietAfterTwo.recall owner) = [] := by
      fin_cases owner <;> rfl
    rw [empty]
    exact fun _ member => (List.not_mem_nil member).elim
  have sendRule : fixedLateRule owner
      ⟨(completeActivation execution owner).application.attempt, bindingEvent owner⟩
        (PhaseSeedScheduler.serviceClocks runtime leaks
          ⟨(completeActivation execution owner).application.attempt, bindingEvent owner⟩ owner
            ((completeActivation execution owner).recall owner)
            ((completeActivation execution owner).observe app owner)) = true := by
    simp only [fixedLateRule, show (completeActivation execution owner).application.attempt =
      originalAttempt from original, ite_true, PhaseSeedScheduler.serviceClocks,
      PhaseSeedScheduler.informationInput, List.getLastD_concat]
    change decide (execution.application.current.native.clock -
      (execution.application.current.native.activatedAt (bindingEvent owner)).getD
        execution.application.current.native.clock = (if owner = alice then 2 else 4)) = true
    rw [clockLate, timer]
    fin_cases owner <;> decide
  obtain ⟨serial, bounded, response, fresh, available, result⟩ :=
    properPolicy_binding_response fixedLateRule (family seed)
      ⟨horizon - firstLatePosition owner - 1, some owner, completeActivation execution owner⟩
      (countedInRaw.trace initial horizon (family seed) pending) owner rfl (bindingEvent owner)
      (bindingEvent_layout owner) observedRequest unsent (Or.inr sendRule)
  refine ⟨serial, bounded, ?_, fresh, available, result⟩
  rw [ownerPolicy, fixedLatePolicy]
  have notZero : (completeActivation execution owner).application.current.native.clock ≠ 0 := by
    change execution.application.current.native.clock ≠ 0
    have positive : 0 < lateClock owner false := by fin_cases owner <;> decide
    omega
  rw [ite_eq_right (fun condition => notZero condition.2)]
  exact response

/-- At the actual eligible late inclusion slot a pending proper packet receives a
true receipt. The private value is read from its original recorded declaration,
including when native normalization immediately closes the commitment phase. -/
theorem proper_late_inclusion (seed : Seeds) (owner : Player) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (position : execution.environmentRecall.length =
      lateIncludePosition owner (seedBits seed owner))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (serial : Nat) (entry : app.PlayerEntry) (retained : entry ∈ execution.recall owner)
    (declared : entry.action =
      phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool (.success true) serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : entry.emitted = some message)
    (timed : (lateClock owner (seedBits seed owner), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks
      (originalCoordinate owner) owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions) :
    ∃ native next,
      family seed execution.environmentRecall (execution.observeEnvironment app) =
        PMF.pure (.include message.id) ∧
      message.payload.packet.call =
        .commitment (bindingEvent owner) (owner, .prepared serial) ∧
      execution.network.lookup message.id = some message ∧
      handle runtime execution.application.current.native
        ⟨message.id, .commitment (bindingEvent owner) (owner, .prepared serial)⟩ = some native ∧
      native.accepted (.inr (bindingEvent owner)) = some (owner, .prepared serial) ∧
      native.config.outputs (bindingEvent owner) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success true : PublicationResult (simpleExpr.Val .bool))) ∧
      next = ({ execution.application with current :=
        execution.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize ∧
      app.handle execution.application message = some next ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
        (execution.includePending app message.id) := by
  classical
  have rawTrace := countedMenu.toRawTrace initial horizon (family seed) trace
  have original : execution.application.attempt = originalAttempt := request.1.symm
  let material : app.Submission :=
    ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), some ⟨.bool, true⟩⟩, .none⟩
  obtain ⟨actual, actualEmission, sender, call⟩ := PhaseCount.recalled_submission_emitted
    runtime leaks initial horizon (family seed) rawTrace owner entry retained material
    (by rw [declared]; rfl)
  have same : actual = message := Option.some.inj (actualEmission.symm.trans emitted)
  subst actual
  obtain ⟨native, next, input, _authored, tagged, found, timely, chosen, nativeHandled,
      _completed, accepted, normalized, phaseHandled⟩ :=
    original_late_binding_admission seed remaining execution trace owner position request message
      timed (owner, .prepared serial) call
  have command : family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.include message.id) := by
    rw [family_apply, chosen]
  have messageRequest : execution.application.SeedRequest owner
      ⟨message.payload.attempt, (bindingEvent owner)⟩ := by
    rw [tagged]
    exact request
  have codeEq : cast (congrArg (EventCode graph.layout) (bindingEvent_layout owner))
      (graph.nodes (bindingEvent owner)) = EventCode.bind (L := simpleExpr)
        (layout := graph.layout) owner BaseTy.bool := by
    fin_cases owner <;> rfl
  have node : nodeView graph (bindingEvent owner) =
      .bind owner .bool (bindingEvent_layout owner) codeEq := by
    fin_cases owner <;> rfl
  obtain ⟨typedNative, _typedNext, handled, _typedCompleted, _typedAccepted, output,
      _typedNormalized, _typedHandled⟩ :=
    recorded_true_binding_accepted (family seed)
      ⟨remaining, none, execution⟩ trace owner
      (bindingEvent owner)
      (bindingEvent_layout owner) codeEq node serial entry retained declared fresh message
      input
      sender call messageRequest timely
  rw [call] at nativeHandled
  have sameTyped : typedNative = native := Option.some.inj (handled.symm.trans nativeHandled)
  subst typedNative
  obtain ⟨actualNative, actualHandled, _actualNormalized, acceptedReceipt⟩ :=
    phase_inclusion_snapshot_bindingAccepted runtime leaks plan (setup.initialLaw.map encodeInputs)
      horizon (family seed) rawTrace message.id message found next phaseHandled
  have sameNative : actualNative = native := by
    rw [call] at actualHandled
    exact Option.some.inj (actualHandled.symm.trans handled)
  subst actualNative
  refine ⟨native, next, command, call, found, handled, accepted, output, normalized,
    phaseHandled, ?_⟩
  have actual := acceptedReceipt (bindingEvent owner) (owner, .prepared serial)
    (by rw [original]; fin_cases owner <;> decide)
    accepted
  simpa only [original, originalCoordinate] using actual

/-- A supported initialized correct-seed branch of the fixed first-late policy
has an actual accepting original binding receipt by the end of its first polling block. -/
theorem fixed_late_accepted_first_block (seed : Seeds) (owner : Player)
    (correct : seedBits seed owner = false)
    (ownerPolicy : players owner = fixedLatePolicy owner)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobWait : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players (firstLatePosition owner + 4)
      initialExecution).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  classical
  rw [app.runRounds_add, PMF.support_bind] at reached
  obtain ⟨execution, beforeReached, future⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨requested, _recalled⟩ := original_first_poll_request_recall profile seed owner
    aliceWait bobWait execution beforeReached
  have original : execution.application.attempt = originalAttempt := requested.1.symm
  obtain ⟨serial, _bounded, response, _freshSlot, freshCandidate, _result⟩ :=
    fixed_late_first_packet profile seed owner correct ownerPolicy aliceWait bobWait
      execution beforeReached
  let observed := completeActivation execution owner
  let action := phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
    (.success true) serial
  let replied := observed.respond app owner action
  obtain ⟨beforeTrace⟩ := counted_profile_trace profile seed (firstLatePosition owner)
    (by fin_cases owner <;> decide) execution beforeReached
  have rawBefore := countedMenu.toRawTrace initial horizon (family seed) beforeTrace
  have valid := raw_native_valid (family seed)
    ⟨horizon - firstLatePosition owner, none, execution⟩ rawBefore
  have count := app.runRounds_environmentRecall_length (family seed) players
    (firstLatePosition owner) initialExecution
    execution beforeReached
  have countEq : execution.environmentRecall.length = firstLatePosition owner := by
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using count
  have clock := original_clock_index seed
    ⟨horizon - firstLatePosition owner, none, execution⟩ rawBefore original
  rw [countEq] at clock
  have clockLate : execution.application.current.native.clock = lateClock owner false := by
    fin_cases owner <;> exact clock
  have timer := original_timer (family seed)
    ⟨horizon - firstLatePosition owner, none, execution⟩ rawBefore original
    (bindingEvent owner) (by
      fin_cases owner
      · exact Or.inl rfl
      · exact Or.inr rfl) requested.2.2.1.1
  have readyEq : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true := by
    change decide (PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, (bindingEvent owner)⟩) = true
    apply decide_eq_true
    apply (execution.application.requests_publicView valid owner _).mpr
    simpa only [originalCoordinate, original] using requested
  have firstCommand : family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.activate owner) := by
    rw [family_first_late_command seed owner _ _ original countEq]
    simp only [correct, pollCommand, ite_true, activateReady, readyEq]
  have firstRound : app.round (family seed) players execution = PMF.pure replied := by
    rw [ReactiveApplication.round, firstCommand, PMF.pure_bind, ReactiveApplication.dispatch,
      completeActivation_law, PMF.pure_bind]
    change (players owner (observed.recall owner) (observed.observe app owner)).map
      (observed.respond app owner) = _
    rw [response, PMF.pure_map]
  have replyReached : replied ∈
      (app.runRounds (family seed) players (firstLatePosition owner + 1)
        initialExecution).support := by
    rw [app.runRounds_add, PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨execution, beforeReached, ?_⟩
    simp only [ReactiveApplication.runRounds, firstRound, PMF.pure_bind,
      PMF.mem_support_pure_iff]
  have requestReply : replied.application.SeedRequest owner (originalCoordinate owner) := by
    apply respond_request runtime leaks observed owner action owner _
    exact requested
  have replyOriginal : replied.application.attempt = originalAttempt := requestReply.1.symm
  have replyLength : replied.environmentRecall.length = firstLatePosition owner + 1 := by
    have length := app.runRounds_environmentRecall_length (family seed) players
      (firstLatePosition owner + 1) initialExecution
      replied replyReached
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using length
  have middleCommand : family seed replied.environmentRecall (replied.observeEnvironment app) =
      PMF.pure (ReactiveApplication.Command.wait : app.Command) := by
    rw [family_middle_late_command seed owner _ _ replyOriginal replyLength]
    rw [quiet_prefix_earlyCommand players seed aliceWait bobWait
      (firstLatePosition owner - 2) replied
      (by convert replyReached using 1; fin_cases owner <;> rfl) (markerOwner owner)]
  let waited : app.Execution := { replied with environmentRecall :=
    replied.environmentRecall ++ [⟨replied.observeEnvironment app, .wait⟩] }
  have middleRound : app.round (family seed) players replied = PMF.pure waited := by
    rw [ReactiveApplication.round, middleCommand, PMF.pure_bind, ReactiveApplication.dispatch,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  have waitedOriginal : waited.application.attempt = originalAttempt := replyOriginal
  have waitedLength : waited.environmentRecall.length = firstLatePosition owner + 2 := by
    change (replied.environmentRecall ++ [_]).length = firstLatePosition owner + 2
    rw [List.length_append, List.length_singleton, replyLength]
  have lastPollCommand : family seed waited.environmentRecall (waited.observeEnvironment app) =
      PMF.pure (ReactiveApplication.Command.wait : app.Command) := by
    rw [family_last_late_poll seed owner _ _ waitedOriginal waitedLength]
    simp only [correct, pollCommand, Bool.false_eq_true, ite_false]
  have lastPollRound : app.round (family seed) players waited = PMF.pure (pollDelay replied) := by
    rw [ReactiveApplication.round, lastPollCommand, PMF.pure_bind, ReactiveApplication.dispatch,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  have waitPair : app.runRounds (family seed) players 2 replied =
      PMF.pure (pollDelay replied) := by
    rw [ReactiveApplication.runRounds, middleRound, PMF.pure_bind,
      ReactiveApplication.runRounds, lastPollRound, PMF.pure_bind, ReactiveApplication.runRounds]
  let atInclusion := pollDelay replied
  have inclusionReached : atInclusion ∈
      (app.runRounds (family seed) players (firstLatePosition owner + 3)
        initialExecution).support := by
    rw [show firstLatePosition owner + 3 = (firstLatePosition owner + 1) + 2 by omega,
      app.runRounds_add, PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨replied, replyReached, ?_⟩
    rw [waitPair]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨inclusionTrace⟩ := counted_profile_trace profile seed (firstLatePosition owner + 3)
    (by fin_cases owner <;> decide) atInclusion inclusionReached
  have inclusionRequest : atInclusion.application.SeedRequest owner (originalCoordinate owner) :=
    requestReply
  have inclusionLength : atInclusion.environmentRecall.length = firstLatePosition owner + 3 := by
    rw [pollDelay_length, replyLength]
  let entry := originalResponseEntry observed owner action
  let material : app.Submission :=
    ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), some ⟨.bool, true⟩⟩, .none⟩
  let packet := app.packet (app.submit observed.application owner material) owner
    (observed.network.known owner) material
  let message := (observed.network.submit owner packet).1
  have emitted : entry.emitted = some message := rfl
  have retained : entry ∈ atInclusion.recall owner := by
    change entry ∈ replied.recall owner
    rw [respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have sender : message.sender = owner := rfl
  have attempt : message.payload.attempt = originalAttempt := by
    change ((observed.application.submit owner material).emit owner
      (observed.network.known owner) material).attempt = originalAttempt
    rw [PhaseCount.emit_after_submit]
    exact original
  have call : message.payload.packet.call = .commitment (bindingEvent owner)
      (owner, .prepared serial) :=
    phase_emit_call (observed.application.submit owner material) owner
      (observed.network.known owner) material
  have own : PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner message = true := by
    simp only [PhaseSeedScheduler.ownPacket, sender, attempt, call, originalCoordinate,
       Payload.event?, and_self, decide_true]
  change PhaseSeedScheduler.ownPacket ⟨originalAttempt, (bindingEvent owner)⟩
    owner message = true at own
  have entryRequest : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner) := by
    apply (execution.application.requests_publicView valid owner _).mpr requested
  have entryClock : entry.beforeView.application.2.native.clock = lateClock owner false := clockLate
  have entryTimer : entry.beforeView.application.2.native.activatedAt (bindingEvent owner) =
      some 0 :=
    timer
  have words := PhaseSeedScheduler.runRounds_wordRecall runtime leaks (family seed) players
    (firstLatePosition owner + 3) initialExecution atInclusion
    (PhaseSeedScheduler.initial_wordRecall runtime leaks initialState)
    inclusionReached
  have timed : (lateClock owner false, message) ∈ (PhaseSeedScheduler.localInput runtime leaks
      (originalCoordinate owner) owner atInclusion.environmentRecall
        (atInclusion.observeEnvironment app)).emissions := by
    rw [PhaseSeedScheduler.localInput_word, words owner (originalCoordinate owner)]
    apply List.mem_flatMap.mpr
    refine ⟨(lateClock owner false, [message]), ?_, by simp only [List.map_cons, List.map_nil,
      List.mem_singleton]⟩
    apply List.mem_map.mpr
    refine ⟨entry, List.mem_filter.mpr ⟨retained, decide_eq_true entryRequest⟩, ?_⟩
    simp only [originalCoordinate, entryClock, entryTimer,
      Option.getD_some, Nat.sub_zero, emitted, Option.toList_some, List.filter_cons, own,
      ite_true, List.filter_nil]
  have entryFresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh :=
    freshCandidate
  have includePosition : lateIncludePosition owner (seedBits seed owner) =
      firstLatePosition owner + 3 := by
    rw [correct]
    fin_cases owner <;> rfl
  have properTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - lateIncludePosition owner (seedBits seed owner), none, atInclusion⟩) := by
    rw [includePosition]
    exact inclusionTrace
  have properPosition : atInclusion.environmentRecall.length =
      lateIncludePosition owner (seedBits seed owner) := by
    rw [includePosition]
    exact inclusionLength
  have properTimed : (lateClock owner (seedBits seed owner), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        atInclusion.environmentRecall (atInclusion.observeEnvironment app)).emissions := by
    rwa [correct]
  obtain ⟨_native, _next, includeCommand, _call, _found, _handled, _accepted, _output, _normalized,
      _phaseHandled, accepted⟩ :=
    proper_late_inclusion seed owner
      (horizon - lateIncludePosition owner (seedBits seed owner)) atInclusion properTrace
        properPosition inclusionRequest
      serial entry retained rfl entryFresh message emitted properTimed
  rw [ReactiveApplication.runRounds, firstRound, PMF.pure_bind,
    show 3 = 2 + 1 by omega, app.runRounds_add, waitPair, PMF.pure_bind,
    ReactiveApplication.runRounds, ReactiveApplication.round, includeCommand, PMF.pure_bind]
      at future
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    ReactiveApplication.runRounds] at future
  cases (PMF.mem_support_pure_iff _ _).mp future
  exact accepted

end Counted

end Vegas.Examples.CommitSeedSignalling
