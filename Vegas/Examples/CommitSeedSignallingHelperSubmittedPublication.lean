/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperEligiblePrefix
import Vegas.Examples.CommitSeedSignallingHelperLatePublication
import Vegas.Examples.CommitSeedSignallingFixedLateSuccess
import Vegas.Examples.CommitSeedSignallingInformation
import Vegas.Pending.PhaseSeedPosteriorResponse
import Vegas.Pending.PhaseSeedEmissionPersistence
import Interaction.ReactiveRoundTrace

/-! # Actual helper responses through eligible inclusion and publication entry -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- The message authored by an actual current binding response is the same
fresh-ID envelope appearing in its actual local emission word. Private
preparation and evidence are preserved literally. -/
theorem helper_submitted_packet_emission (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (candidate : Handle graph)
    (call : material.call.packet = .commitment (bindingEvent alice) candidate) :
    ∃ message : Message Player (CommitAttemptPacket graph),
      (originalResponseEntry execution alice ⟨some material⟩).emitted = some message ∧
      message.payload.packet.call = .commitment (bindingEvent alice) candidate ∧
      (execution.application.current.native.clock, message) ∈
        (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
          (execution.respond app alice ⟨some material⟩).environmentRecall
          ((execution.respond app alice ⟨some material⟩).observeEnvironment app)).emissions := by
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining execution
    alice ⟨some material⟩ trace offered
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have rawResponded := countedMenu.toRawTrace initial horizon (family seed) responded
  have valid := raw_native_valid (family seed) ⟨remaining, some alice, execution⟩ raw
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining (execution.respond app alice ⟨some material⟩) responded
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have stamp := original_timer (family seed) ⟨remaining, some alice, execution⟩ raw original
    (bindingEvent alice) (Or.inl rfl) request.2.2.1.1
  have names : material.call.packet.event? graph = some (originalAddress alice).1.event := by
    rw [call]
    rfl
  obtain ⟨message, identified, emitted⟩ := PhaseSeedCalendar.response_envelope_recorded runtime
    leaks execution valid alice (originalAddress alice) request material names 0 stamp words
  let packet := app.packet (app.submit execution.application alice material) alice
    (execution.network.known alice) material
  let actual := (execution.network.submit alice packet).1
  have actualInput : actual ∈
      (execution.respond app alice ⟨some material⟩).network.inputs := by
    change actual ∈ execution.network.inputs ++ [actual]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have messageInput := PhaseSeedScheduler.localInput_emission_authentic runtime leaks
    (execution.respond app alice ⟨some material⟩) (originalCoordinate alice) alice words
      (app.history_inputRecall initial horizon (family seed) rawResponded) _ message emitted
  have same : message = actual := app.input_identifier_injective_history initial horizon
    (family seed) ⟨remaining, none, execution.respond app alice ⟨some material⟩⟩ rawResponded
      message actual messageInput.1 actualInput identified
  subst message
  refine ⟨actual, rfl, ?_, ?_⟩
  · exact (phase_emit_call (execution.application.submit alice material) alice
      (execution.network.known alice) material).trans call
  · simpa only [Nat.sub_zero, originalAddress] using emitted

/-- A retained literal proper current declaration determines the semantic
output of the actual admitted native packet. Its old own word is unrestricted. -/
theorem helper_true_packet_native_output (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (position : execution.environmentRecall.length =
      lateIncludePosition alice (seedBits seed alice))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (serial : Nat) (entry : app.PlayerEntry) (retained : entry ∈ execution.recall alice)
    (declared : entry.action =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool (.success true) serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : entry.emitted = some message)
    (timed : (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        execution.environmentRecall (execution.observeEnvironment app)).emissions)
    (native : EventGraphRuntime.State graph)
    (handled : handle runtime execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    native.config.outputs (bindingEvent alice) = some
      (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
        (PublicationResult.success true : PublicationResult (simpleExpr.Val .bool))) := by
  obtain ⟨typedNative, _next, _command, call, _lookup, accepted, _handle, output, _normalized,
      _phaseHandled, _receipt⟩ := proper_late_inclusion seed alice remaining execution trace
    position request serial entry retained declared fresh message emitted timed
  rw [call] at handled
  have same : native = typedNative := Option.some.inj (handled.symm.trans accepted)
  subst native
  exact output

/-- A current eligible clock-two binding response reaches the real publication
suffix after the actual three commands. The current material is arbitrary;
the normalized native admission result is derived from the same run. -/
theorem helper_clock_two_submitted_publication (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = false)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (identified : marker.id = (bob, 0)) (permitted : PhaseCount.permits [] marker = true)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (candidate : Handle graph)
    (call : material.call.packet = .commitment (bindingEvent alice) candidate)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players 3
      (execution.respond app alice ⟨some material⟩)).support) :
    ∃ before native message,
      before ∈ (app.runRounds (family seed) players 2
        (execution.respond app alice ⟨some material⟩)).support ∧
      Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
        (some ⟨remaining - 2, none, before⟩)) ∧
      before.application.SeedRequest alice (originalCoordinate alice) ∧
      PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob before ∧
      before.environmentRecall.length = lateIncludePosition alice (seedBits seed alice) ∧
      (originalResponseEntry execution alice ⟨some material⟩) ∈ before.recall alice ∧
      (originalResponseEntry execution alice ⟨some material⟩).emitted = some message ∧
      (lateClock alice (seedBits seed alice), message) ∈
        (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
          before.environmentRecall (before.observeEnvironment app)).emissions ∧
      next ∈ (app.round (family seed) players before).support ∧
      handle runtime before.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      native.accepted (.inr (bindingEvent alice)) = some candidate ∧
      next.application.current.native = native ∧
      next.application.phases <:+ [publicationPhase] ∧
      next.application.current.excluded = ∅ ∧
      ∀ recalled ∈ next.recall alice, ∀ coordinate : CommitAttemptEvent graph,
        coordinate.event = revealEvent alice →
          ¬ PhaseRuntimeState.requests recalled.beforeView.application.2 alice coordinate := by
  obtain ⟨message, entryEmitted, packetCall, timed⟩ := helper_submitted_packet_emission seed
    remaining execution fixed request material offered candidate call
  rw [show 3 = 2 + 1 by decide, app.runRounds_add, PMF.support_bind] at reached
  obtain ⟨before, preceding, following⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨requested, bobAccepted, position, recalled, ⟨beforeTrace⟩⟩ :=
    helper_clock_two_eligible_prefix seed remaining execution mixed fixed bit request clock quiet
      marker input sender identified permitted ⟨some material⟩ offered players covered before
        preceding
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining execution
    alice ⟨some material⟩ fixed offered
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining (execution.respond app alice ⟨some material⟩) responded
  have retained := PhaseSeedScheduler.runRounds_emissions_prefix runtime leaks (family seed) players
    2 (execution.respond app alice ⟨some material⟩) before words preceding alice
      (originalCoordinate alice)
  have eligible : (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        before.environmentRecall (before.observeEnvironment app)).emissions := by
    rw [clock] at timed
    have actual := retained.subset timed
    simpa only [bit, lateClock, ite_true, Bool.false_eq_true, ite_false] using actual
  have entryRecorded : originalResponseEntry execution alice ⟨some material⟩ ∈
      before.recall alice := by
    rw [recalled, respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have last : next ∈ (app.round (family seed) players before).support := by
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using following
  obtain ⟨native, handled, accepted, nativeEq, suffix, clear, unserved⟩ :=
    helper_late_binding_publication_entry seed (remaining - 2) before beforeTrace position requested
      message eligible candidate packetCall bobAccepted players next last
  exact ⟨before, native, message, preceding, ⟨beforeTrace⟩, requested, bobAccepted, position,
    entryRecorded, entryEmitted, eligible, last, handled, accepted, nativeEq, suffix, clear,
      unserved⟩

/-- A current eligible clock-three response is admitted by the actual next
round. Its literal source record is retained at the new publication suffix. -/
theorem helper_clock_three_submitted_publication (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (position : execution.environmentRecall.length = 10)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (candidate : Handle graph)
    (call : material.call.packet = .commitment (bindingEvent alice) candidate)
    (players : Player → app.Policy) (next : app.Execution)
    (reached : next ∈ (app.round (family seed) players
      (execution.respond app alice ⟨some material⟩)).support) :
    ∃ native message,
      (originalResponseEntry execution alice ⟨some material⟩).emitted = some message ∧
      handle runtime (execution.respond app alice ⟨some material⟩).application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      native.accepted (.inr (bindingEvent alice)) = some candidate ∧
      next.application.current.native = native ∧
      next.application.phases <:+ [publicationPhase] ∧
      next.application.current.excluded = ∅ ∧
      ∀ recalled ∈ next.recall alice, ∀ coordinate : CommitAttemptEvent graph,
        coordinate.event = revealEvent alice →
          ¬ PhaseRuntimeState.requests recalled.beforeView.application.2 alice coordinate := by
  obtain ⟨message, entryEmitted, packetCall, timed⟩ := helper_submitted_packet_emission seed
    remaining execution fixed request material offered candidate call
  obtain ⟨requested, bobReceipt, includedPosition, ⟨repliedTrace⟩⟩ :=
    helper_clock_three_eligible_prefix seed remaining execution fixed bit request position
      bobAccepted ⟨some material⟩ offered
  have eligible : (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        (execution.respond app alice ⟨some material⟩).environmentRecall
        ((execution.respond app alice ⟨some material⟩).observeEnvironment app)).emissions := by
    rw [clock] at timed
    simpa only [bit, lateClock, ite_true] using timed
  obtain ⟨native, handled, accepted, nativeEq, suffix, clear, unserved⟩ :=
    helper_late_binding_publication_entry seed remaining
      (execution.respond app alice ⟨some material⟩) repliedTrace includedPosition requested message
        eligible candidate packetCall bobReceipt players next reached
  exact ⟨native, message, entryEmitted, handled, accepted, nativeEq, suffix, clear, unserved⟩

/-- The actual proper clock-two response reaches a genuine clear publication
entry with Alice's stored successful value after three rounds. This preserves
all original earlier callbacks and the same future player kernels. -/
theorem helper_clock_two_proper_publication (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = false)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (identified : marker.id = (bob, 0)) (permitted : PhaseCount.permits [] marker = true)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (serial : Nat)
    (declared : (⟨some material⟩ : app.Action) =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool (.success true) serial)
    (fresh : (execution.observe app alice).application.1.candidates (.prepared serial) = .fresh)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players 3
      (execution.respond app alice ⟨some material⟩)).support) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining - 3, none, next⟩)) ∧
      next.application.phases <:+ [publicationPhase] ∧
      next.application.current.native.config.outputs (bindingEvent alice) = some
        (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
          (PublicationResult.success true : PublicationResult (simpleExpr.Val .bool))) ∧
      next.application.current.excluded = ∅ ∧
      ∀ recalled ∈ next.recall alice, ∀ coordinate : CommitAttemptEvent graph,
        coordinate.event = revealEvent alice →
          ¬ PhaseRuntimeState.requests recalled.beforeView.application.2 alice coordinate := by
  have materialEq := congrArg (fun response : app.Action => response.transmission) declared
  change some material = some
    (⟨⟨.commitment (bindingEvent alice) (alice, .prepared serial), some ⟨.bool, true⟩⟩, .none⟩ :
      WitnessedSubmission graph) at materialEq
  have call : material.call.packet =
      .commitment (bindingEvent alice) (alice, .prepared serial) := by
    rw [Option.some.inj materialEq]
  obtain ⟨before, native, message, preceding, ⟨beforeTrace⟩, requested, _bobAccepted, position,
      entryRecorded, entryEmitted, eligible, _last, handled, _accepted, nativeEq, suffix, clear,
        unserved⟩ := helper_clock_two_submitted_publication seed remaining execution mixed fixed
    bit request clock quiet marker input sender identified permitted material offered
      (alice, .prepared serial) call players covered next reached
  have entryDeclared : (originalResponseEntry execution alice ⟨some material⟩).action =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool (.success true) serial :=
    declared
  have output := helper_true_packet_native_output seed (remaining - 2) before beforeTrace position
    requested serial (originalResponseEntry execution alice ⟨some material⟩) entryRecorded
      entryDeclared fresh message entryEmitted eligible native handled
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed)
    beforeTrace).1
  have enough : 3 ≤ remaining := by
    rw [position] at accounted
    change lateIncludePosition alice (seedBits seed alice) + (remaining - 2) = 64 at accounted
    rw [bit] at accounted
    change 7 + (remaining - 2) = 64 at accounted
    omega
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining execution
    alice ⟨some material⟩ fixed offered
  have wholeTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 3) + 3, none, execution.respond app alice ⟨some material⟩⟩) := by
    rw [show (remaining - 3) + 3 = remaining by omega]
    exact responded
  obtain ⟨nextTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    (remaining - 3) 3 (execution.respond app alice ⟨some material⟩) next wholeTrace reached
  refine ⟨⟨nextTrace⟩, suffix, ?_, clear, unserved⟩
  rw [nativeEq]
  exact output

/-- The actual proper clock-three response reaches the corresponding genuine
clear publication entry in one round, without changing the old silent word. -/
theorem helper_clock_three_proper_publication (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (position : execution.environmentRecall.length = 10)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (serial : Nat)
    (declared : (⟨some material⟩ : app.Action) =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool (.success true) serial)
    (fresh : (execution.observe app alice).application.1.candidates (.prepared serial) = .fresh)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (next : app.Execution)
    (reached : next ∈ (app.round (family seed) players
      (execution.respond app alice ⟨some material⟩)).support) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining - 1, none, next⟩)) ∧
      next.application.phases <:+ [publicationPhase] ∧
      next.application.current.native.config.outputs (bindingEvent alice) = some
        (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
          (PublicationResult.success true : PublicationResult (simpleExpr.Val .bool))) ∧
      next.application.current.excluded = ∅ ∧
      ∀ recalled ∈ next.recall alice, ∀ coordinate : CommitAttemptEvent graph,
        coordinate.event = revealEvent alice →
          ¬ PhaseRuntimeState.requests recalled.beforeView.application.2 alice coordinate := by
  have materialEq := congrArg (fun response : app.Action => response.transmission) declared
  change some material = some
    (⟨⟨.commitment (bindingEvent alice) (alice, .prepared serial), some ⟨.bool, true⟩⟩, .none⟩ :
      WitnessedSubmission graph) at materialEq
  have call : material.call.packet =
      .commitment (bindingEvent alice) (alice, .prepared serial) := by
    rw [Option.some.inj materialEq]
  obtain ⟨native, message, entryEmitted, handled, _accepted, nativeEq, suffix, clear, unserved⟩ :=
    helper_clock_three_submitted_publication seed remaining execution fixed bit request clock
      position bobAccepted material offered (alice, .prepared serial) call players next reached
  obtain ⟨actual, actualEmitted, _packetCall, timed⟩ := helper_submitted_packet_emission seed
    remaining execution fixed request material offered (alice, .prepared serial) call
  have same : actual = message := Option.some.inj (actualEmitted.symm.trans entryEmitted)
  subst actual
  obtain ⟨requested, _bobReceipt, includedPosition, ⟨repliedTrace⟩⟩ :=
    helper_clock_three_eligible_prefix seed remaining execution fixed bit request position
      bobAccepted ⟨some material⟩ offered
  let entry := originalResponseEntry execution alice ⟨some material⟩
  have recorded : entry ∈ (execution.respond app alice ⟨some material⟩).recall alice := by
    rw [respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have entryDeclared : entry.action = phaseBindingResponse runtime leaks alice (bindingEvent alice)
      .bool (.success true) serial := declared
  have eligible : (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        (execution.respond app alice ⟨some material⟩).environmentRecall
        ((execution.respond app alice ⟨some material⟩).observeEnvironment app)).emissions := by
    rw [clock] at timed
    simpa only [bit, lateClock, ite_true] using timed
  have output := helper_true_packet_native_output seed remaining
    (execution.respond app alice ⟨some material⟩) repliedTrace includedPosition requested serial
      entry recorded entryDeclared fresh message entryEmitted eligible native handled
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed)
    repliedTrace).1
  have positive : 0 < remaining := by
    rw [ReactiveApplication.respond_environmentRecall, position] at accounted
    change 10 + remaining = 64 at accounted
    omega
  have beforeTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - 1) + 1, none, execution.respond app alice ⟨some material⟩⟩) := by
    rw [show remaining - 1 + 1 = remaining by omega]
    exact repliedTrace
  obtain ⟨nextTrace⟩ := countedMenu.trace_round initial horizon (family seed) players covered
    (remaining - 1) (execution.respond app alice ⟨some material⟩) next beforeTrace reached
  refine ⟨⟨nextTrace⟩, suffix, ?_, clear, unserved⟩
  rw [nativeEq]
  exact output

end Vegas.Examples.CommitSeedSignalling
