/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperInitialRecall
import Interaction.ReactiveAnchoredTrace

/-! # Omitting the sole eligible original callback forces exclusion -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

private def aliceClock (entry : app.PlayerEntry) : Nat :=
  entry.beforeView.application.2.native.clock -
    (entry.beforeView.application.2.native.activatedAt aliceBinding).getD
      entry.beforeView.application.2.native.clock

private theorem alice_record_prior_clock_fresh (seed : Seeds) (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩))
    (earlier : List app.PlayerEntry) (entry : app.PlayerEntry) (later : List app.PlayerEntry)
    (recalled : execution.recall alice = earlier ++ entry :: later)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice)) :
    aliceClock entry ∉ (PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate alice)
      alice earlier).map Prod.fst := by
  classical
  obtain ⟨before, prior, _kept, active, past, viewed, _allowed⟩ :=
    rawMenu.recorded_response_at initial horizon (family seed) ⟨0, none, execution⟩ trace alice
      earlier entry later recalled
  have raw := rawMenu.toRawTrace initial horizon (family seed) prior
  have valid := raw_native_valid (family seed) before raw
  rw [viewed] at requested
  change PhaseRuntimeState.requests before.execution.application.publicView alice
    (originalCoordinate alice) at requested
  have request := (before.execution.application.requests_publicView valid alice _).mp requested
  have calendar := original_service_clocks_prefix rawMenu seed before prior alice active request
  simp only [ite_true] at calendar
  have unique := (by decide : ([0, 2, 3] : List Nat).Nodup).sublist calendar.sublist
  rw [PhaseSeedScheduler.serviceClocks, PhaseSeedScheduler.informationInput, past, ← viewed]
    at unique
  change ((PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate alice) alice earlier).map
    Prod.fst ++ [aliceClock entry]).Nodup at unique
  rw [List.nodup_append_comm] at unique
  exact (List.nodup_cons.mp unique).1

private theorem alice_record_clock_member (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (recorded : entry ∈ past)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice)) :
    aliceClock entry ∈ (PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate alice)
      alice past).map Prod.fst := by
  classical
  simp only [PhaseSeedScheduler.ownerWord, List.map_map, Function.comp_def]
  exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨recorded, decide_eq_true requested⟩, rfl⟩

private theorem alice_original_record_clock (seed : Seeds) (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩))
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice)) :
    aliceClock entry = entry.beforeView.application.2.native.clock := by
  obtain ⟨before, prior, _kept, _active, viewed, _allowed, _later⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed) ⟨0, none, execution⟩ trace
      alice entry recorded
  have raw := rawMenu.toRawTrace initial horizon (family seed) prior
  have valid := raw_native_valid (family seed) before raw
  unfold aliceClock
  rw [viewed] at requested ⊢
  change PhaseRuntimeState.requests before.execution.application.publicView alice
    (originalCoordinate alice) at requested
  have request := (before.execution.application.requests_publicView valid alice _).mp requested
  have stamp := original_timer (family seed) before raw request.1.symm aliceBinding (Or.inl rfl)
    request.2.2.1.1
  change before.execution.application.current.native.activatedAt aliceBinding = some 0 at stamp
  change before.execution.application.current.native.clock -
    (before.execution.application.current.native.activatedAt aliceBinding).getD
      before.execution.application.current.native.clock = _
  rw [stamp, Option.getD_some, Nat.sub_zero]
  rfl

private theorem actual_silent_record_emits_none (seed : Seeds) (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩))
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (omitted : entry.action.transmission = none) : entry.emitted = none := by
  let fallback : Player → app.Policy := fun _ => app.silentPolicy
  let players := ReactiveApplication.anchoredPolicy execution fallback
  have actual := ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace initial horizon
    (family seed) fallback (rawMenu.toRawTrace initial horizon (family seed) trace)
  have reached : execution ∈
      (app.runRounds (family seed) players horizon initialExecution).support :=
    by simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind, Nat.sub_zero,
      initialExecution] using actual.2
  have faithful := (app.silentEmission_invariant players alice).runRounds (family seed) horizon
    initialExecution execution (fun found member => (List.not_mem_nil member).elim) reached
  exact faithful entry recorded omitted

private theorem alice_silent_clock_has_no_emission (seed : Seeds) (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩))
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice))
    (omitted : entry.action.transmission = none)
    (clock : Nat) (sameClock : aliceClock entry = clock)
    (message : Message Player (CommitAttemptPacket graph)) :
    (clock, message) ∉ (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice)
      alice execution.environmentRecall (execution.observeEnvironment app)).emissions := by
  classical
  intro emitted
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks rawMenu initial horizon
    (family seed) 0 execution trace
  rw [PhaseSeedScheduler.localInput_word, words alice (originalCoordinate alice)] at emitted
  obtain ⟨record, recordMember, packetMember⟩ := List.mem_flatMap.mp emitted
  obtain ⟨packet, packetMember, pairEq⟩ := List.mem_map.mp packetMember
  have samePacket : packet = message := congrArg Prod.snd pairEq
  subst packet
  obtain ⟨sender, entryMember, recordEq⟩ := List.mem_map.mp recordMember
  obtain ⟨retained, senderRequested⟩ := List.mem_filter.mp entryMember
  have senderRequest : PhaseRuntimeState.requests sender.beforeView.application.2 alice
      (originalCoordinate alice) := of_decide_eq_true senderRequested
  have senderPacket : message ∈ sender.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice) := by
    simpa only [← recordEq] using packetMember
  have actualEmission := Option.mem_toList.mp (List.mem_filter.mp senderPacket).1
  have senderClock : aliceClock sender = clock :=
    (congrArg Prod.fst recordEq).trans (congrArg Prod.fst pairEq)
  obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp recorded
  rw [recalled] at retained
  rcases List.mem_append.mp retained with previous | current
  · have fresh := alice_record_prior_clock_fresh seed execution trace earlier entry later recalled
      requested
    have present := alice_record_clock_member earlier sender previous senderRequest
    rw [senderClock, ← sameClock] at present
    exact fresh present
  · rcases List.mem_cons.mp current with same | subsequent
    · subst sender
      have absent := actual_silent_record_emits_none seed execution trace entry recorded omitted
      rw [absent] at actualEmission
      cases actualEmission
    · obtain ⟨between, tail, position⟩ := List.mem_iff_append.mp subsequent
      have senderRecall : execution.recall alice =
          (earlier ++ entry :: between) ++ sender :: tail := by
        rw [recalled, position]
        simp only [List.append_assoc, List.cons_append]
      have fresh := alice_record_prior_clock_fresh seed execution trace
        (earlier ++ entry :: between) sender tail senderRecall senderRequest
      have present := alice_record_clock_member (earlier ++ entry :: between) entry
        (List.mem_append_right _ (List.mem_cons_self)) requested
      rw [sameClock, ← senderClock] at present
      exact fresh present

/-- An actual initial WAIT followed by silence at Alice's unique eligible
original callback forces her final exclusion, independently of all later raw play. -/
theorem alice_eligible_wait_excluded (seed : Seeds) (execution : app.Execution)
    (trace : rawProtocol.Trace (some ⟨0, none, execution⟩))
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩))
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (request : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice))
    (clock : entry.beforeView.application.2.native.clock = lateClock alice (seedBits seed alice))
    (omitted : entry.action.transmission = none) :
    alice ∈ execution.application.current.excluded := by
  have noEarly := alice_initial_wait_snapshot_empty seed 0 execution trace fixed quiet
  have unaccepted : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice
      execution := by
    intro accepted
    obtain ⟨message, emitted⟩ := original_binding_accepted_late_of_empty_snapshot seed 0 execution
      fixed alice noEarly accepted
    have sameClock : aliceClock entry = lateClock alice (seedBits seed alice) :=
      (alice_original_record_clock seed execution fixed entry recorded request).trans clock
    exact alice_silent_clock_has_no_emission seed execution fixed entry recorded request omitted
      _ sameClock message emitted
  by_contra survives
  have raw := rawMenu.toRawTrace initial horizon (family seed) fixed
  have length := app.raw_trace_horizon initial horizon (family seed) raw
  change execution.environmentRecall.length + 0 = horizon at length
  have late : 22 ≤ execution.environmentRecall.length := by
    change execution.environmentRecall.length + 0 = 64 at length
    omega
  have closed := original_attempt_retired seed ⟨0, none, execution⟩ raw late
  have receipt := (survivor_original_receipt_or_open (family seed) ⟨0, none, execution⟩ raw
    alice survives).resolve_left closed
  exact unaccepted receipt

end Vegas.Examples.CommitSeedSignalling
