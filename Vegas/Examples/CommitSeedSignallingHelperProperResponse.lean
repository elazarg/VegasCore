/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperSafeContinuation
import Vegas.Examples.CommitSeedSignallingHelperQuietRecall

/-! # Literal current actions of the seed-informed proper continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- At the known useful callback the whole proper comparator emits one actual
fresh TRUE declaration. Its unsent premise is derived from the entire literal
old own word, rather than supplied as a continuation-policy assumption. -/
theorem helper_eligible_proper_response (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool) (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (afterWait : bit = true → ∃ helper ∈ execution.recall alice,
      helper.beforeView.application.2.native.clock = 2 ∧ helper.action.transmission = none) :
    ∃ serial, serial < horizon ∧
      properPolicy (helperTimingRule bit) alice (execution.recall alice)
          (execution.observe app alice) =
        PMF.pure (phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool
          (.success true) serial) ∧
      reactiveFreshSlot (execution.observe app alice).application.1 = some serial ∧
      execution.application.current.native.candidates.lookup (alice, .prepared serial) = .fresh ∧
      (execution.respond app alice
        (phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool
          (.success true) serial)).application.current.native.bindingResult
            (alice, .prepared serial) .bool = .success true := by
  have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
  have empty : app.outputs (execution.recall alice) = [] := by
    cases bit with
    | false =>
        exact alice_clock_two_initial_wait_outputs_empty seed remaining execution rawFixed request
          clock quiet
    | true =>
        obtain ⟨helper, remembered, helperClock, waited⟩ := afterWait rfl
        exact alice_clock_three_after_wait_outputs_empty seed remaining execution rawFixed
          request clock quiet helper remembered helperClock waited
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have requested : execution.application.SeedRequest alice
      ⟨execution.application.attempt, bindingEvent alice⟩ := by
    simpa only [originalCoordinate, original] using request
  have unsent : ∀ message ∈ app.outputs (execution.recall alice),
      PhaseCount.event? message.payload ≠
        some ⟨execution.application.attempt, bindingEvent alice⟩ := by
    rw [empty]
    exact fun _ member => (List.not_mem_nil member).elim
  have timer := original_timer (family seed) ⟨remaining, some alice, execution⟩
    (rawMenu.toRawTrace initial horizon (family seed) rawFixed)
    original aliceBinding (Or.inl rfl) request.2.2.1.1
  have choose : helperTimingRule bit alice
      ⟨execution.application.attempt, bindingEvent alice⟩
        (PhaseSeedScheduler.serviceClocks runtime leaks
          ⟨execution.application.attempt, bindingEvent alice⟩ alice
            (execution.recall alice) (execution.observe app alice)) = true := by
    simp only [helperTimingRule, original, ite_true, PhaseSeedScheduler.serviceClocks,
      PhaseSeedScheduler.informationInput, List.getLastD_concat]
    change decide (execution.application.current.native.clock -
      (execution.application.current.native.activatedAt aliceBinding).getD
        execution.application.current.native.clock = if bit then 3 else 2) = true
    rw [timer, clock]
    cases bit <;> decide
  exact properPolicy_binding_response (helperTimingRule bit) (family seed)
    ⟨remaining, some alice, execution⟩ (countedInRaw.trace initial horizon (family seed) fixed)
      alice rfl (bindingEvent alice) (bindingEvent_layout alice) requested unsent (Or.inr choose)

/-- With the late-three seed, the proper whole comparator really waits at
clock two. It subsequently reads the same actual own word at clock three. -/
theorem helper_clock_two_proper_wait (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2) :
    properPolicy (helperTimingRule true) alice (execution.recall alice)
      (execution.observe app alice) = PMF.pure ⟨none⟩ := by
  let clocks := PhaseSeedScheduler.serviceClocks runtime leaks
    ⟨execution.application.attempt, bindingEvent alice⟩ alice (execution.recall alice)
      (execution.observe app alice)
  have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have timer := original_timer (family seed) ⟨remaining, some alice, execution⟩
    (rawMenu.toRawTrace initial horizon (family seed) rawFixed)
    original aliceBinding (Or.inl rfl) request.2.2.1.1
  have last : clocks.getLastD 0 = 2 := by
    simp only [clocks, PhaseSeedScheduler.serviceClocks, PhaseSeedScheduler.informationInput,
      List.getLastD_concat]
    change execution.application.current.native.clock -
      (execution.application.current.native.activatedAt aliceBinding).getD
        execution.application.current.native.clock = 2
    rw [timer, clock]
    rfl
  have calendar := original_service_clocks_prefix countedMenu seed
    ⟨remaining, some alice, execution⟩ fixed alice rfl request
  have names : (⟨execution.application.attempt, bindingEvent alice⟩ : CommitAttemptEvent graph) =
      originalCoordinate alice := by
    rw [original]
    rfl
  have calendarHere : clocks <+: [0, 2, 3] := by
    simpa only [clocks, names, ite_true] using calendar
  have notFirst : clocks.length ≠ 1 := by
    intro first
    obtain ⟨time, single⟩ := List.length_eq_one_iff.mp first
    rw [single] at calendarHere last
    have zero : time = 0 := (List.cons_prefix_cons.mp calendarHere).1
    change time = 2 at last
    omega
  have notChosen : helperTimingRule true alice
      ⟨execution.application.attempt, bindingEvent alice⟩ clocks = false := by
    simp only [helperTimingRule, original, ite_true, last]
    decide
  have valid := raw_native_valid (family seed) ⟨remaining, some alice, execution⟩
    (rawMenu.toRawTrace initial horizon (family seed) rawFixed)
  have requested : execution.application.SeedRequest alice
      ⟨execution.application.attempt, bindingEvent alice⟩ := by
    simpa only [originalCoordinate, original] using request
  have service := phaseCountServicePolicy_binding setup .concurrentReveals runtime leaks bounds
    trueBindingLaw (helperTimingRule true) 0 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    execution valid alice (bindingEvent alice) .bool (bindingEvent_layout alice) requested
  change properPolicy (helperTimingRule true) alice _ _ = _ at service
  rw [service]
  dsimp only [PhaseCount.bindingServiceReference, PhaseCount.bindingServiceBase]
  simp only [zero_add, mix_zero]
  change (if clocks.length = 1 then _ else if helperTimingRule true alice
    (⟨execution.application.attempt, bindingEvent alice⟩ : CommitAttemptEvent graph) clocks
      then _ else PMF.pure (⟨none⟩ : app.Action)) = _
  rw [ite_eq_right notFirst, notChosen]
  rfl
end Vegas.Examples.CommitSeedSignalling
