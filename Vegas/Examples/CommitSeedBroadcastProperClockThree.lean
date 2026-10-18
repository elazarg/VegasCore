/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastKnownEligibleContinuation
import Vegas.Examples.CommitSeedBroadcastProperTimingContext

/-! # Literal past consistency of the later proper original continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- At the second original callback, the clock-three comparator really waits,
with its literal whole own input and the original initial response retained. -/
theorem scheduled_proper_clock_three_wait_at_two (selected : app.Scheduler)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (rawMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2)
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner)) :
    scheduledProperPolicy 3 owner (execution.recall owner) (execution.observe app owner) =
      PMF.pure ⟨none⟩ := by
  classical
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have requested : execution.application.SeedRequest owner
      ⟨execution.application.attempt, bindingEvent owner⟩ := by
    simpa only [original, originalCoordinate] using request
  have timer := original_timer selected ⟨remaining, some owner, execution⟩
    (rawMenu.toRawTrace initial horizon selected trace) original owner request.2.2.1.1
  have notFirst : (PhaseSeedScheduler.serviceClocks runtime leaks
      ⟨execution.application.attempt, bindingEvent owner⟩ owner (execution.recall owner)
        (execution.observe app owner)).length ≠ 1 := by
    change PhaseRuntimeState.requests first.beforeView.application.2 owner
      ⟨originalAttempt, bindingEvent owner⟩ at firstRequest
    simp [PhaseSeedScheduler.serviceClocks, PhaseSeedScheduler.informationInput,
      PhaseSeedScheduler.ownerWord, word, original, firstRequest]
  have wait : lateAtRule 3 owner ⟨execution.application.attempt, bindingEvent owner⟩
      (PhaseSeedScheduler.serviceClocks runtime leaks
        ⟨execution.application.attempt, bindingEvent owner⟩ owner (execution.recall owner)
          (execution.observe app owner)) = false := by
    simp only [lateAtRule, original, ite_true, PhaseSeedScheduler.serviceClocks,
      PhaseSeedScheduler.informationInput, List.getLastD_concat]
    change decide (execution.application.current.native.clock -
      (execution.application.current.native.activatedAt (bindingEvent owner)).getD
        execution.application.current.native.clock = 3) = false
    rw [timer, clock]
    rfl
  have valid := raw_native_valid selected ⟨remaining, some owner, execution⟩
    (rawMenu.toRawTrace initial horizon selected trace)
  have service := phaseCountServicePolicy_binding setup .concurrentReveals runtime leaks bounds
    trueBindingLaw (lateAtRule 3) 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    execution valid owner (bindingEvent owner) .bool (bindingEvent_layout owner) requested
  change properPolicy (lateAtRule 3) owner _ _ = _ at service
  rw [scheduledProperPolicy, ite_eq_right (fun enabled => by
    have zero : execution.application.current.native.clock = 0 := enabled.2.1
    omega), service]
  dsimp only [PhaseCount.bindingServiceReference, PhaseCount.bindingServiceBase]
  simp only [zero_add, mix_zero, ite_eq_right notFirst, wait, Bool.false_eq_true, ite_false]

/-- The two literal WAIT records at clocks zero and two are consistent with
the whole proper clock-three continuation, including their original views. -/
theorem proper_clock_three_two_waits_consistent
    (current : app.Control) (trace : rawProtocol.Trace (some current)) (owner : Player)
    (first second : app.PlayerEntry)
    (word : current.execution.recall owner = [first, second])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (secondClock : second.beforeView.application.2.native.clock = 2)
    (firstSilent : first.action.transmission = none)
    (secondSilent : second.action.transmission = none) :
    (scheduledProperPolicy 3 owner).Consistent (current.execution.recall owner) := by
  classical
  have firstAction : first.action = (⟨none⟩ : app.Action) := by
    have eta : first.action = ⟨first.action.transmission⟩ := by cases first.action; rfl
    exact eta.trans (congrArg ReactiveApplication.Action.mk firstSilent)
  have initialPast : (scheduledProperPolicy 3 owner).Consistent [first] := by
    apply ReactiveApplication.Policy.Consistent.snoc first .nil
    rw [scheduledProperPolicy, ite_eq_left ⟨firstRequest.1.symm, firstClock, by decide⟩,
      PMF.mem_support_pure_iff]
    exact firstAction
  obtain ⟨before, beforeTrace, _retained, active, ownPast, viewed, _allowed⟩ :=
    rawMenu.recorded_response_at initial horizon scheduler current trace owner [first] second []
      (by simpa only [List.append_nil, List.singleton_append] using word)
  have valid := raw_native_valid scheduler before
    (rawMenu.toRawTrace initial horizon scheduler beforeTrace)
  have publicRequest := secondRequest
  rw [viewed] at publicRequest
  have request := (before.execution.application.requests_publicView valid owner
    (originalCoordinate owner)).mp publicRequest
  have clock : before.execution.application.current.native.clock = 2 := by
    rw [viewed] at secondClock
    exact secondClock
  have literal := scheduled_proper_clock_three_wait_at_two scheduler before.remaining
    before.execution owner (by simpa only [← active] using beforeTrace) request clock first ownPast
      firstRequest
  have secondAction : second.action = (⟨none⟩ : app.Action) := by
    have eta : second.action = ⟨second.action.transmission⟩ := by cases second.action; rfl
    exact eta.trans (congrArg ReactiveApplication.Action.mk secondSilent)
  rw [word]
  apply ReactiveApplication.Policy.Consistent.snoc second initialPast
  rw [viewed, ← ownPast, literal, PMF.mem_support_pure_iff]
  exact secondAction

end Vegas.Examples.CommitSeedBroadcast
