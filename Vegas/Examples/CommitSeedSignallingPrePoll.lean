/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingLateBeliefs
import Vegas.Examples.CommitSeedSignallingUnresolved
import Vegas.Examples.CommitSeedSignallingHalfSuccess

/-! # No original late emission before its scheduled polling block -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

theorem original_callback_clock_before_bob_poll (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (early : current.execution.environmentRecall.length ≤ 12) :
    current.execution.application.current.native.clock ≤ 3 := by
  obtain ⟨past, view, command, recalled, actor⟩ :=
    app.active_environment_entry initial horizon (family seed) current trace owner active
  have commandEq : command = .activate owner := by
    cases command <;> simp_all only [ReactiveApplication.Command.actor?,
      Option.some.injEq, reduceCtorEq]
  subst command
  have entryOriginal : view.application.attempt = originalAttempt := by
    exact earlier_original_attempt seed current trace original ⟨view, .activate owner⟩
      (by rw [recalled]; exact List.mem_append_right _ (List.mem_singleton_self _))
  have commands := family_commands seed current trace
  rw [recalled] at commands
  have chosen := (app.commandConsistent_snoc choose seed past ⟨view, .activate owner⟩).mp commands
  have selected : originalCommand seed past.length past view = .activate owner := by
    rw [choose_original seed past view entryOriginal] at chosen
    exact chosen.2
  have length : current.execution.environmentRecall.length = past.length + 1 := by
    rw [recalled, List.length_append, List.length_singleton]
  have positions := original_activation_positions seed past.length past view owner (by omega)
    selected
  have clock := original_clock_index seed current trace original
  rw [length] at clock
  rcases positions with position | position | position | position | position | position |
    position | position
  all_goals first
    | omega
    | rw [position] at clock
      norm_num [originalClock, originalClockFrom, originalTick] at clock
      omega

theorem original_emission_callback (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (clock : Nat) (message : Message Player (CommitAttemptPacket graph))
    (emitted : (clock, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    ∃ (before : app.Control)
      (prior : (rawMenu.protocol initial horizon (family seed)).Trace (some before)),
      TracePrefix prior trace ∧ before.actor = some owner ∧
      before.execution.application.attempt = originalAttempt ∧
      before.execution.application.current.native.clock = clock := by
  classical
  obtain ⟨_accounted, supported⟩ := rawMenu.roundSupported_uniform initial horizon
    (family seed) trace
  change execution ∈ (app.roundsFrom initial (family seed) rawMenu.uniformResponses
    execution.environmentRecall.length).support at supported
  rw [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind] at supported
  have word := PhaseSeedScheduler.runRounds_wordRecall runtime leaks (family seed)
    rawMenu.uniformResponses execution.environmentRecall.length initialExecution execution
    (PhaseSeedScheduler.initial_wordRecall runtime leaks initialState) supported
  rw [PhaseSeedScheduler.localInput_word, word, PhaseSeedScheduler.ownerWord] at emitted
  obtain ⟨pair, recalled, contained⟩ := List.mem_flatMap.mp emitted
  obtain ⟨entry, requested, pairEq⟩ := List.mem_map.mp recalled
  obtain ⟨recorded, requested⟩ := List.mem_filter.mp requested
  subst pair
  obtain ⟨actual, _actualMember, pairEq⟩ := List.mem_map.mp contained
  have elapsed := congrArg Prod.fst pairEq
  obtain ⟨before, prior, retained, active, observed, _allowed, _rest⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed)
      ⟨remaining, none, execution⟩ trace owner entry recorded
  have request : before.execution.application.SeedRequest owner (originalCoordinate owner) := by
    rw [observed] at requested
    exact (before.execution.application.requests_publicView
      (raw_native_valid (family seed) before
        (rawMenu.toRawTrace initial horizon (family seed) prior)) owner
      (originalCoordinate owner)).mp (of_decide_eq_true requested)
  have original : before.execution.application.attempt = originalAttempt := request.1.symm
  have binding : bindingEvent owner = aliceBinding ∨ bindingEvent owner = bobBinding := by
    fin_cases owner
    · exact Or.inl rfl
    · exact Or.inr rfl
  have timer := original_timer (family seed) before
    (rawMenu.toRawTrace initial horizon (family seed) prior) original (bindingEvent owner)
      binding request.2.2.1.1
  have physicalClock : before.execution.application.current.native.clock = clock := by
    rw [observed] at elapsed
    change before.execution.application.current.native.clock -
      (before.execution.application.current.native.activatedAt (bindingEvent owner)).getD
        before.execution.application.current.native.clock = clock at elapsed
    simpa only [timer, Option.getD_some, Nat.sub_zero] using elapsed
  exact ⟨before, prior, retained, active, original, physicalClock⟩

/-- A quiet initialized prefix before Bob's late polling has no already
accepted original Bob binding. This is a pointwise native-history statement. -/
theorem bob_binding_unaccepted_before_poll (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (early : execution.environmentRecall.length ≤ 12)
    (empty : ∀ entry, execution.environmentRecall[2]? = some entry →
      ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ bob) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob execution := by
  intro accepted
  obtain ⟨message, emitted⟩ := original_binding_accepted_late_of_empty_snapshot seed remaining
    execution trace bob empty accepted
  obtain ⟨before, prior, retained, active, original, clock⟩ :=
    original_emission_callback seed remaining execution trace bob _ message emitted
  have pastPrefix := tracePrefix_environment_prefix seed before ⟨remaining, none, execution⟩
    prior trace retained
  have bounded : before.execution.environmentRecall.length ≤ 12 :=
    pastPrefix.length_le.trans early
  have tooEarly := original_callback_clock_before_bob_poll seed before
    (rawMenu.toRawTrace initial horizon (family seed) prior) bob active original bounded
  rw [clock] at tooEarly
  have late : 4 ≤ lateClock bob (seed.2 (originalAddress bob)) := by
    cases seed.2 (originalAddress bob) <;> decide
  omega

end Vegas.Examples.CommitSeedSignalling
