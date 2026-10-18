/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFailedBindingValue
import Vegas.Examples.CommitSeedSignallingHelperEligiblePrefix
import Vegas.Examples.CommitSeedSignallingHelperLatePublication
import Vegas.Examples.CommitSeedSignallingHelperCountedTrace
import Vegas.Examples.CommitSeedSignallingHelperBindingValue
import Vegas.Examples.CommitSeedSignallingHelperTypedReceipt
import Vegas.Examples.CommitSeedSignallingOriginalLastInput
import Vegas.Pending.PhaseRecordedBindingMaterial
import Interaction.ReactiveSchedulerFinishSeed

/-! # Unusable private preparations at an eligible original helper declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem helper_observation_authored_input (selected : app.Scheduler)
    (current : app.Control)
    (trace : (rawMenu.protocol initial horizon selected).Trace (some current))
    (helper : app.PlayerEntry)
    (remembered : helper ∈ current.execution.recall alice ∨
      helper.beforeView = current.execution.observe app alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger) :
    marker ∈ current.execution.network.inputs := by
  have raw := rawMenu.toRawTrace initial horizon selected trace
  have now := app.retained_envelopes_mem_inputs current.execution
    (app.history_provenance initial horizon selected raw)
    (app.history_inputRecall initial horizon selected raw)
  rcases remembered with old | viewed
  · obtain ⟨before, prior, kept, _active, viewed, _allowed, _later⟩ :=
      rawMenu.recorded_response_prefix initial horizon selected current trace alice helper old
    have rawBefore := rawMenu.toRawTrace initial horizon selected prior
    have previous := app.retained_envelopes_mem_inputs before.execution
      (app.history_provenance initial horizon selected rawBefore)
      (app.history_inputRecall initial horizon selected rawBefore)
    rw [viewed] at visible
    have input : marker ∈ before.execution.network.inputs := by
      rcases visible with leaked | ledger
      · exact previous.leaked alice marker leaked
      · exact previous.ledger marker ledger
    obtain ⟨entry, recorded, _material, _transmitted, emitted, _packet⟩ :=
      (app.history_provenance initial horizon selected rawBefore).inputs marker input
    have earlier := app.reaches_recall_prefix initial horizon selected
      (rawMenu.reaches_raw initial horizon selected kept.reachesWithin) before current rfl rfl
        marker.sender
    have output : marker ∈ app.outputs (current.execution.recall marker.sender) :=
      List.mem_filterMap.mpr ⟨entry, earlier.subset recorded, emitted⟩
    rw [← app.history_inputRecall initial horizon selected raw marker.sender] at output
    exact (List.mem_filter.mp output).1
  · rw [viewed] at visible
    rcases visible with leaked | ledger
    · exact now.leaked alice marker leaked
    · exact now.ledger marker ledger

/-- The exact private declaration fixes its failed meaning permanently.
Evidence requests are arbitrary; failure is read from the supplied opening,
not inferred from a receipt or a later strategic prescription. -/
theorem recorded_unusable_helper_binding_result (selected : app.Scheduler)
    (current : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some current))
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall alice)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw simpleExpr))
    (evidence : EvidenceRequest graph)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment event (alice, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (unusable : (opening.bind fun raw => raw.as? .bool) = none) :
    current.execution.application.current.native.bindingResult
      (alice, .prepared serial) .bool = .failure := by
  have result := phase_recorded_material_binding_result runtime leaks countedMenu initial horizon
    selected current trace alice event .bool serial opening evidence entry recorded declared fresh
  simpa only [unusable, Option.elim_none] using result

/-- The actual late include writes the unusable typed value, and clear
settlement retains that value in the publication suffix. The selected native
handler, rather than a successful-preparation assumption, supplies completion. -/
theorem helper_unusable_late_publication_entry (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (position : execution.environmentRecall.length =
      lateIncludePosition alice (seedBits seed alice))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (serial : Nat) (opening : Option (Raw simpleExpr)) (evidence : EvidenceRequest graph)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment aliceBinding (alice, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (unusable : (opening.bind fun raw => raw.as? .bool) = none)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        execution.environmentRecall (execution.observeEnvironment app)).emissions)
    (call : message.payload.packet.call = .commitment aliceBinding (alice, .prepared serial))
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (players : Player → app.Policy) (next : app.Execution)
    (reached : next ∈ (app.round (family seed) players execution).support) :
    next.application.phases <:+ [publicationPhase] ∧
      aliceBinding ∈ next.application.current.native.config.cut.completed ∧
      bobBinding ∈ next.application.current.native.config.cut.completed ∧
      next.application.current.native.config.outputs aliceBinding = some .failure := by
  have meaning := recorded_unusable_helper_binding_result (family seed)
    ⟨remaining, none, execution⟩ trace entry recorded aliceBinding serial opening evidence
      declared fresh unusable
  have called : message.payload.packet.call =
      .commitment (bindingEvent alice) (alice, .prepared serial) := call
  obtain ⟨native, handled, _accepted, nativeEq, suffix, _clear, _unserved⟩ :=
    helper_late_binding_publication_entry seed remaining execution trace position request message
      emitted (alice, .prepared serial) called bobAccepted players next reached
  have rawHandled : handle runtime execution.application.current.native
      ⟨message.id, .commitment aliceBinding (alice, .prepared serial)⟩ = some native := by
    simpa only [call] using handled
  have codeEq : cast (congrArg (EventCode graph.layout) binding_layouts.1)
      (graph.nodes aliceBinding) = EventCode.bind (L := simpleExpr)
        (layout := graph.layout) alice BaseTy.bool := by rfl
  have node : nodeView graph aliceBinding = .bind alice .bool binding_layouts.1 codeEq := by
    rfl
  obtain ⟨_ready, configEq⟩ := runtime.handle_commitment_config_result
    execution.application.current.native native message.id aliceBinding
      (alice, .prepared serial) alice .bool binding_layouts.1 codeEq node rawHandled
  have bobDone := original_bob_receipt_completed (family seed) ⟨remaining, none, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace) request.1.symm bobAccepted
  have aliceNext : aliceBinding ∈ native.config.cut.completed := by
    rw [configEq]
    exact Finset.mem_insert_self _ _
  have bobNext := handle_completed_subset runtime execution.application.current.native native
    ⟨message.id, message.payload.packet.call⟩ handled bobDone
  refine ⟨suffix, ?_, ?_, ?_⟩
  · rwa [nativeEq]
  · rwa [nativeEq]
  · rw [nativeEq, configEq, Config.complete_output_same, meaning]
    rfl

private theorem helper_recorded_eligible_emission (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice))
    (clock : entry.beforeView.application.2.native.clock = lateClock alice (seedBits seed alice))
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : entry.emitted = some message)
    (packet : PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true) :
    (lateClock alice (seedBits seed alice), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        execution.environmentRecall (execution.observeEnvironment app)).emissions := by
  classical
  obtain ⟨before, prior, _kept, _active, viewed, _offered, _later⟩ :=
    countedMenu.recorded_response_prefix initial horizon (family seed) _ trace alice entry recorded
  have raw := countedMenu.toRawTrace initial horizon (family seed) prior
  have valid := raw_native_valid (family seed) before raw
  have publicRequest := requested
  rw [viewed] at publicRequest
  have request := (before.execution.application.requests_publicView valid alice
    (originalCoordinate alice)).mp publicRequest
  have timer := original_timer (family seed) before raw request.1.symm aliceBinding (Or.inl rfl)
    request.2.2.1.1
  have age : entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt aliceBinding).getD
        entry.beforeView.application.2.native.clock = lateClock alice (seedBits seed alice) := by
    rw [viewed] at clock ⊢
    change before.execution.application.current.native.clock -
      (before.execution.application.current.native.activatedAt aliceBinding).getD
        before.execution.application.current.native.clock = _
    rw [timer, Option.getD_some, Nat.sub_zero]
    exact clock
  have row : (lateClock alice (seedBits seed alice), entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice)) ∈
      PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate alice) alice
        (execution.recall alice) := by
    apply List.mem_map.mpr
    refine ⟨entry, List.mem_filter.mpr ⟨recorded, decide_eq_true requested⟩, ?_⟩
    exact congrArg (fun elapsed => (elapsed, entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice))) age
  have member : message ∈ entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice) := by
    rw [emitted]
    exact List.mem_filter.mpr ⟨List.mem_singleton_self _, packet⟩
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining execution trace
  rw [PhaseSeedScheduler.localInput_word, words alice (originalCoordinate alice)]
  exact List.mem_flatMap.mpr ⟨_, row, List.mem_map.mpr ⟨message, member, rfl⟩⟩

/-- The real three-command continuation at the first eligible helper slot
installs a permanent failed binding. Every remaining physical continuation
retains it, with no restriction on its later values or responses. -/
theorem helper_clock_two_unusable_binding_run (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = false)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (identified : marker.id = (bob, 0)) (permitted : PhaseCount.permits [] marker = true)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining
      (execution.respond app alice ⟨some material⟩)).support) :
    final.application.current.native.config.outputs aliceBinding = some .failure := by
  classical
  have currentRequest : execution.application.SeedRequest alice
      ⟨execution.application.attempt, aliceBinding⟩ := by
    simpa only [request.1.symm, originalCoordinate, bindingEvent, ite_true] using request
  obtain ⟨serial, opening, evidence, shape, _bounded, fresh⟩ :=
    counted_submission_binding_shape (family seed) remaining execution alice trace aliceBinding
      .bool binding_layouts.1 currentRequest material offered
  have failed : (opening.bind fun raw => raw.as? .bool) = none := by
    rwa [shape] at unusable
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have enough := family_requested_remaining seed ⟨remaining, some alice, execution⟩ raw
    (originalCoordinate alice) alice request
  change 9 < remaining at enough
  have decomposition : remaining = 2 + (remaining - 2) := by omega
  rw [decomposition, app.runRounds_add] at reached
  obtain ⟨before, gap, following⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨pending, bobAccepted, position, recallEq, ⟨beforeTrace⟩⟩ :=
    helper_clock_two_eligible_prefix seed remaining execution mixed trace bit request clock quiet
      marker input sender identified permitted ⟨some material⟩ offered players covered before gap
  have rest : remaining - 2 = (remaining - 3) + 1 := by omega
  rw [rest] at following
  change final ∈ ((app.round (family seed) players before).bind
    (app.runRounds (family seed) players (remaining - 3))).support at following
  obtain ⟨included, inclusion, future⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ following)
  let action : app.Action := ⟨some material⟩
  let entry := originalResponseEntry execution alice action
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(alice, execution.network.nextSerial alice),
      app.packet (app.submit execution.application alice material) alice
        (execution.network.known alice) material⟩
  have recorded : entry ∈ before.recall alice := by
    rw [recallEq, respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have declared : entry.action =
      ⟨some ⟨⟨.commitment aliceBinding (alice, .prepared serial), opening⟩, evidence⟩⟩ := by
    exact congrArg (fun submitted => (⟨some submitted⟩ : app.Action)) shape
  have called : message.payload.packet.call = .commitment aliceBinding
      (alice, .prepared serial) := by
    change ((execution.application.submit alice material).emit alice
      (execution.network.known alice) material).packet.call = _
    rw [phase_emit_call, shape]
  have tagged : message.payload.attempt = originalAttempt := by
    change ((execution.application.submit alice material).emit alice
      (execution.network.known alice) material).attempt = _
    rw [PhaseCount.emit_after_submit]
    exact request.1.symm
  have packet : PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true := by
    apply decide_eq_true
    refine ⟨rfl, tagged, ?_⟩
    rw [called]
    rfl
  have valid := raw_native_valid (family seed) ⟨remaining, some alice, execution⟩ raw
  have requested : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice) :=
    (execution.application.requests_publicView valid alice (originalCoordinate alice)).mpr request
  have eligible : entry.beforeView.application.2.native.clock =
      lateClock alice (seedBits seed alice) := by
    change execution.application.current.native.clock = _
    rw [clock, bit]
    rfl
  have timed := helper_recorded_eligible_emission seed (remaining - 2) before beforeTrace entry
    recorded requested eligible message rfl packet
  obtain ⟨suffix, _aliceDone, _bobDone, output⟩ :=
    helper_unusable_late_publication_entry seed (remaining - 2) before beforeTrace position pending
      entry recorded serial opening evidence declared fresh failed message timed called bobAccepted
        players included inclusion
  have retained := publication_tail_run_keepsStore (family seed) players (remaining - 3) included
    final suffix future
  exact retained (.inr aliceBinding) .failure output

/-- At the other eligible slot the inclusion is the very next command.
Its factual original Bob receipt makes the failed Alice binding permanent;
later raw responses cannot roll it back. -/
theorem helper_clock_three_unusable_binding_run (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (position : execution.environmentRecall.length = 10)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining
      (execution.respond app alice ⟨some material⟩)).support) :
    final.application.current.native.config.outputs aliceBinding = some .failure := by
  classical
  have currentRequest : execution.application.SeedRequest alice
      ⟨execution.application.attempt, aliceBinding⟩ := by
    simpa only [request.1.symm, originalCoordinate, bindingEvent, ite_true] using request
  obtain ⟨serial, opening, evidence, shape, _bounded, fresh⟩ :=
    counted_submission_binding_shape (family seed) remaining execution alice trace aliceBinding
      .bool binding_layouts.1 currentRequest material offered
  have failed : (opening.bind fun raw => raw.as? .bool) = none := by
    rwa [shape] at unusable
  obtain ⟨pending, bobAfter, count, ⟨post⟩⟩ := helper_clock_three_eligible_prefix seed remaining
    execution trace bit request position bobAccepted ⟨some material⟩ offered
  have enough := family_requested_remaining seed ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace) (originalCoordinate alice) alice
      request
  change 9 < remaining at enough
  have decomposition : remaining = (remaining - 1) + 1 := by omega
  rw [decomposition] at reached
  change final ∈ ((app.round (family seed) players
    (execution.respond app alice ⟨some material⟩)).bind
      (app.runRounds (family seed) players (remaining - 1))).support at reached
  obtain ⟨included, inclusion, future⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  let action : app.Action := ⟨some material⟩
  let after := execution.respond app alice action
  let entry := originalResponseEntry execution alice action
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(alice, execution.network.nextSerial alice),
      app.packet (app.submit execution.application alice material) alice
        (execution.network.known alice) material⟩
  have recorded : entry ∈ after.recall alice := by
    rw [respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have declared : entry.action =
      ⟨some ⟨⟨.commitment aliceBinding (alice, .prepared serial), opening⟩, evidence⟩⟩ := by
    exact congrArg (fun submitted => (⟨some submitted⟩ : app.Action)) shape
  have called : message.payload.packet.call = .commitment aliceBinding
      (alice, .prepared serial) := by
    change ((execution.application.submit alice material).emit alice
      (execution.network.known alice) material).packet.call = _
    rw [phase_emit_call, shape]
  have tagged : message.payload.attempt = originalAttempt := by
    change ((execution.application.submit alice material).emit alice
      (execution.network.known alice) material).attempt = _
    rw [PhaseCount.emit_after_submit]
    exact request.1.symm
  have packet : PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true := by
    apply decide_eq_true
    refine ⟨rfl, tagged, ?_⟩
    rw [called]
    rfl
  have valid := raw_native_valid (family seed) ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace)
  have requested : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice) :=
    (execution.application.requests_publicView valid alice (originalCoordinate alice)).mpr request
  have clock := original_clock_index seed ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace) request.1.symm
  have eligible : entry.beforeView.application.2.native.clock =
      lateClock alice (seedBits seed alice) := by
    change execution.application.current.native.clock = _
    rw [clock, position, bit]
    rfl
  have timed := helper_recorded_eligible_emission seed remaining after post entry recorded
    requested eligible message rfl packet
  obtain ⟨suffix, _aliceDone, _bobDone, output⟩ :=
    helper_unusable_late_publication_entry seed remaining after post count pending entry recorded
      serial opening evidence declared fresh failed message timed called bobAfter players included
        inclusion
  have retained := publication_tail_run_keepsStore (family seed) players (remaining - 1) included
    final suffix future
  exact retained (.inr aliceBinding) .failure output

/-- An unusable declaration at the known eligible slot has minus-one value.
The complete native suffix is disintegrated from its original posterior;
the earlier helper observation determines the original bit on every member. -/
theorem raw_failed_helper_binding_assessed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool)
    (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (marker : Message Player (CommitAttemptPacket graph)) (sender : marker.sender = bob)
    (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true) :
    expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, execution.respond app alice ⟨some material⟩⟩))
        (fun state => netPayoff state alice) = -1 := by
  classical
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler remaining execution
    alice ⟨some material⟩ trace offered
  let after := execution.respond app alice (⟨some material⟩ : app.Action)
  let history : countedProtocol.History := ⟨some ⟨remaining, none, after⟩, responded⟩
  let profile := countedAssessmentProfile assessment
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view := by
    intro owner past view response selected
    exact countedMenu.decode_embedPolicy_covered initial horizon scheduler owner (profile owner)
      past view response selected
  have law := raw_terminal_state_law assessment.strategy
    (countedInRaw.history initial horizon scheduler history)
  change (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy
      (countedInRaw.history initial horizon scheduler history)).map History.state =
    app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, after⟩) at law
  rw [← law, expect_map, ← expect_constant _ (-1 : ℝ)]
  apply expect_congr_on_support
  intro final supported
  have retained := supported
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
    (rawMenu.bounded initial horizon scheduler)] at retained
  have sameRun := (countedInRaw.actionRestriction initial horizon scheduler).runFrom_law
    profile assessment.strategy (raw_equilibrium_extends_counted assessment equilibrium)
      (2 * horizon + 1) history
  change (countedModel.runBehavioralFrom profile (2 * horizon + 1) history).map
      (countedInRaw.history initial horizon scheduler) =
    rawModel.runBehavioralFrom assessment.strategy (2 * horizon + 1)
      (countedInRaw.history initial horizon scheduler history) at sameRun
  rw [← sameRun, PMF.support_map] at retained
  obtain ⟨countedFinal, reached, same⟩ := retained
  have sourceLaw := countedMenu.run_eq_finish initial horizon scheduler profile
    (2 * horizon + 1) history (by
      have bound := app.trace_bound initial horizon scheduler
        (countedMenu.toRawTrace initial horizon scheduler history.trace)
      exact (Nat.le_add_left _ _).trans bound)
  have physical : countedFinal.state ∈
      ((countedModel.runBehavioralFrom profile (2 * horizon + 1) history).map
        History.state).support := by
    rw [PMF.support_map]
    exact ⟨countedFinal, reached, rfl⟩
  rw [sourceLaw] at physical
  change countedFinal.state ∈ (app.finish initial horizon scheduler players
    (some ⟨remaining, none, after⟩)).support at physical
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at physical
  change countedFinal.state ∈ ((app.runRounds scheduler players remaining after).map
    app.finished).support at physical
  obtain ⟨ending, rounds, stateEq⟩ := PMF.support_map .. ▸ physical
  have realization :
      (implementation.posterior after.environmentRecall).bind
        (fun seed => app.runRounds (family seed) players remaining after) =
      app.runRounds scheduler players remaining after := by
    have realized := implementation.realize players remaining after
    simp only [implementation, app.schedulerMixture_runJoint, PMF.map_bind,
      PMF.map_comp, Function.comp_def] at realized
    change (implementation.posterior after.environmentRecall).bind
      (fun seed => (app.runRounds (family seed) players remaining after).map id) =
        app.runRounds scheduler players remaining after at realized
    simpa only [PMF.map_id] using realized
  rw [← realization, PMF.support_bind] at rounds
  obtain ⟨seed, originalPosterior, fixedRun⟩ := Set.mem_iUnion₂.mp rounds
  have supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support :=
    originalPosterior
  obtain ⟨_originalSupport, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some alice, execution⟩ trace seed supportedSeed
  have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
  have seedRead : seedBits seed alice = true ↔
      ∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts := by
    rcases remembered with old | current
    · obtain ⟨post⟩ := countedMenu.trace_respond initial horizon (family seed) remaining execution
        alice ⟨some material⟩ fixed offered
      have stillRecorded := app.respond_recall_mono execution alice alice
        (⟨some material⟩ : app.Action) old
      exact recorded_helper_seed_iff_receipt seed remaining after
        (countedInRaw.trace initial horizon (family seed) post) helper stillRecorded helperRequest
          helperClock marker sender addressed visible
    · subst helper
      exact alice_helper_clock_two_seed seed ⟨remaining, some alice, execution⟩ rawFixed rfl
        request helperClock marker sender addressed visible
  have bitEq : seedBits seed alice = bit := by
    have same := seedRead.trans readout
    cases actual : seedBits seed alice <;> cases bit <;> simp_all
  have seen : helper ∈ execution.recall alice ∨
      helper.beforeView = execution.observe app alice := by
    rcases remembered with old | current
    · exact Or.inl old
    · exact Or.inr (current ▸ rfl)
  have input := helper_observation_authored_input (family seed)
    ⟨remaining, some alice, execution⟩ rawFixed helper seen marker visible
  have failed : ending.application.current.native.config.outputs aliceBinding = some .failure := by
    cases bit with
    | false =>
        have clockHere : execution.application.current.native.clock = 2 := by
          simpa only [Bool.false_eq_true, ite_false] using clock
        have indexed := original_first_late_input_index seed
          ⟨remaining, some alice, execution⟩ rawFixed alice rfl request.1.symm clockHere
        have early : execution.environmentRecall.length ≤ 12 := by
          change execution.environmentRecall.length =
            4 + if seedBits seed alice then 3 else 1 at indexed
          rw [bitEq] at indexed
          norm_num at indexed
          omega
        obtain ⟨identified, permitted⟩ := observed_helper_packet_permission seed
          ⟨remaining, some alice, execution⟩ trace rawFixed request early marker input sender
        exact helper_clock_two_unusable_binding_run seed remaining execution
          (countedInRaw.trace initial horizon scheduler trace) fixed bitEq request clockHere quiet
            marker input sender identified permitted material offered unusable players covered
              ending fixedRun
    | true =>
        have clockHere : execution.application.current.native.clock = 3 := by
          simpa only [ite_true] using clock
        have position := alice_original_clock_three_input_index seed
          ⟨remaining, some alice, execution⟩ rawFixed rfl request.1.symm clockHere
        have bobAccepted := counted_helper_bob_binding_accepted seed
          ⟨remaining, some alice, execution⟩ trace fixed request quiet (by omega) (by omega)
            marker input sender
        exact helper_clock_three_unusable_binding_run seed remaining execution fixed bitEq request
          position bobAccepted material offered unusable players ending fixedRun
  have state := congrArg History.state same
  change countedFinal.state = final.state at state
  have finalState : final.state = some (⟨0, none, ending⟩ : app.Control) :=
    state.symm.trans stateEq.symm
  have terminal := rawModel.runBehavioralTerminalFrom_support_terminal canonicalCertificate
    assessment.strategy (countedInRaw.history initial horizon scheduler history) final supported
  have rawFinal := rawMenu.toRawTrace initial horizon scheduler final.trace
  rw [finalState] at terminal rawFinal
  have complete := scheduler_completesPlay ⟨0, none, ending⟩ rawFinal terminal
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun value _ => PhaseCount.countClean_initial runtime leaks value)
      countedFinal.trace
  rw [state, finalState] at clean
  have own : OwnPermitted alice ending :=
    ⟨clean.1, fun message member _ => clean.2 message member⟩
  exact standing_bad_terminal_payoff final ⟨0, none, ending⟩ finalState complete alice own
    (by simpa only [ite_true] using failed)

open Classical in
/-- The failure value is constant on the entire raw helper information
fiber. Counted prehistory is reconstructed from the actual common input;
foreign raw history is not required to be globally clean. -/
theorem raw_failed_helper_binding_fiber_committed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool)
    (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (marker : Message Player (CommitAttemptPacket graph)) (sender : marker.sender = bob)
    (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (choice : rawModel.Choice alice site.1) (selected : choice.1 = some ⟨some material⟩)
    (target : rawModel.InformationHistory alice site.1) :
    expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
        ((assessment.strategy alice).commit site.1 choice)) target.1) (rawPayoff alice) = -1 := by
  let retained : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace) :=
    ⟨target.1, target.2.trans atSite⟩
  obtain ⟨count, next, state, recalled, observed⟩ :=
    raw_information_control_of_counted_view source remaining execution alice current retained
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩) :=
    current ▸ source.trace
  have targetTrace : rawProtocol.Trace (some ⟨count, some alice, next⟩) := state ▸ target.1.trace
  obtain ⟨sourceSeed, sourceSupported⟩ :=
    (implementation.posterior execution.environmentRecall).support_nonempty
  obtain ⟨_sourceSupport, ⟨sourceFixed⟩⟩ := menu_original_posterior_trace rawMenu
    ⟨remaining, some alice, execution⟩ (countedInRaw.trace initial horizon scheduler sourceTrace)
      sourceSeed sourceSupported
  obtain ⟨targetSeed, targetSupported⟩ :=
    (implementation.posterior next.environmentRecall).support_nonempty
  obtain ⟨_targetSupport, ⟨targetFixed⟩⟩ := menu_original_posterior_trace rawMenu
    ⟨count, some alice, next⟩ targetTrace targetSeed targetSupported
  have sourceSeen : helper ∈ execution.recall alice ∨
      helper.beforeView = execution.observe app alice := by
    rcases remembered with old | current
    · exact Or.inl old
    · exact Or.inr (current ▸ rfl)
  have targetRemembered : helper ∈ next.recall alice ∨
      helper = originalResponseEntry next alice ⟨none⟩ := by
    rcases remembered with old | current
    · exact Or.inl (recalled.symm ▸ old)
    · have same : originalResponseEntry next alice ⟨none⟩ =
          originalResponseEntry execution alice ⟨none⟩ := by
        simp only [originalResponseEntry, observed, Option.map_none]
      exact Or.inr (current.trans same.symm)
  have targetSeen : helper ∈ next.recall alice ∨
      helper.beforeView = next.observe app alice := by
    rcases targetRemembered with old | current
    · exact Or.inl old
    · exact Or.inr (current ▸ rfl)
  have sourceInput := helper_observation_authored_input scheduler
    ⟨remaining, some alice, execution⟩ (countedInRaw.trace initial horizon scheduler sourceTrace)
      helper sourceSeen marker visible
  have targetInput := helper_observation_authored_input scheduler
    ⟨count, some alice, next⟩ targetTrace helper targetSeen marker visible
  have clockBound : execution.application.current.native.clock ≤ 3 := by
    split at clock <;> omega
  obtain ⟨countedTarget⟩ := raw_helper_input_counted_trace sourceSeed targetSeed
    ⟨remaining, some alice, execution⟩ ⟨count, some alice, next⟩ sourceTrace sourceFixed targetTrace
      targetFixed request clockBound recalled observed marker sender sourceInput targetInput
  have sourceValid := raw_native_valid scheduler ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
  have targetRaw := rawMenu.toRawTrace initial horizon scheduler targetTrace
  have targetValid := raw_native_valid scheduler ⟨count, some alice, next⟩ targetRaw
  have publicSource := (execution.application.requests_publicView sourceValid alice
    (originalCoordinate alice)).mpr request
  have publicTarget : PhaseRuntimeState.requests next.application.publicView alice
      (originalCoordinate alice) := by
    change PhaseRuntimeState.requests (next.observe app alice).application.2 alice _
    rw [observed]
    exact publicSource
  have requested := (next.application.requests_publicView targetValid alice
    (originalCoordinate alice)).mp publicTarget
  have clockHere : next.application.current.native.clock = if bit then 3 else 2 := by
    exact (congrArg (fun view : app.PlayerView => view.application.2.native.clock)
      observed).trans clock
  have offeredHere : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (next.recall alice) (next.observe app alice) := by
    rw [recalled, observed]
    exact offered
  have value := raw_failed_helper_binding_assessed_value assessment equilibrium count next
    countedTarget requested bit clockHere (recalled.symm ▸ quiet) helper targetRemembered
      helperRequest helperClock material offeredHere unusable marker sender addressed visible
        readout
  have bound := app.trace_bound initial horizon scheduler targetRaw
  have enough : app.rank horizon target.1.state ≤ 2 * horizon + 1 := by
    rw [state]
    exact (Nat.le_add_left _ _).trans bound
  have projection := rawMenu.run_local_law_finish_of_information initial horizon scheduler
    assessment.strategy target.1 alice count next state site.1 target.2 (PMF.pure choice)
      (2 * horizon) enough
  change (rawModel.runBehavioralFrom
    (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
      ((assessment.strategy alice).commit site.1 choice)) (2 * horizon + 1) target.1).map
        History.state = _ at projection
  rw [PMF.pure_map, selected, Option.getD_some, PMF.pure_bind] at projection
  have terminalProjection : (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy alice
        ((assessment.strategy alice).commit site.1 choice)) target.1).map History.state =
      app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (some ⟨count, none, next.respond app alice ⟨some material⟩⟩) := by
    rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
      (rawMenu.bounded initial horizon scheduler)]
    exact projection
  have expected := congrArg (fun law : PMF app.ProtocolState =>
    expect law (fun state => netPayoff state alice)) terminalProjection
  rw [expect_map] at expected
  exact expected.trans value

open Classical in
/-- The actual belief integrates the unusable-preparation loss at either
known eligible helper input. This includes the entire raw information fiber
and does not require positive assessed reach or a prescribed foreign tail. -/
theorem raw_failed_helper_binding_context_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool)
    (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (marker : Message Player (CommitAttemptPacket graph)) (sender : marker.sender = bob)
    (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (choice : rawModel.Choice alice site.1) (selected : choice.1 = some ⟨some material⟩) :
    (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
      ((assessment.strategy alice).commit site.1 choice) = -1 := by
  have integrable := assessment.continuationContext_integrable_of_bounded_terminal
    canonicalCertificate site (rawPayoff alice) 6 (fun final _ => rawPayoff_abs_le alice final)
      ((assessment.strategy alice).commit site.1 choice)
  change (assessment.continuationContextWith
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff alice)).value
      ((assessment.strategy alice).commit site.1 choice) = -1
  rw [assessment.continuationContextWith_value_tower
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site (rawPayoff alice)
      ((assessment.strategy alice).commit site.1 choice) integrable,
    ← expect_constant (assessment.belief alice site) (-1 : ℝ)]
  apply expect_congr_on_support
  intro target _
  exact raw_failed_helper_binding_fiber_committed_value assessment equilibrium source remaining
    execution current request bit clock quiet helper remembered helperRequest helperClock material
      offered unusable marker sender addressed visible readout site atSite choice selected target

end Vegas.Examples.CommitSeedSignalling
