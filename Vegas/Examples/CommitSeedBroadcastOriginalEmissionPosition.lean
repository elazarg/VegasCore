/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalLateAdmission
import Interaction.ReactiveRecordedEnvironmentPrefix

/-! # Eligible original callbacks precede their actual include positions -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem eligible_turn_before_include (owner rank : Player) (good : Bool) (index : Nat)
    (turn : index ∈ [owner.val, (if good then 5 else 11) + rank.val, 18 + rank.val])
    (clock : originalClock index = lateClock good) :
    index < (if good then 14 else 21) + rank.val := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at turn
  rcases turn with rfl | rfl | rfl
  all_goals fin_cases owner <;> fin_cases rank <;> cases good
  all_goals norm_num [originalClock, originalClockFrom, originalTick, lateClock] at clock
  all_goals norm_num

/-- A retained original callback fixes its actual command position and relative
clock, even after the original attempt has retired. -/
theorem original_recorded_callback_clock (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (index : Nat) (bounded : index < execution.environmentRecall.length)
    (callback : PhaseSeedScheduler.callback runtime leaks (originalCoordinate owner) owner
      execution.environmentRecall[index]) :
    index ∈ originalTurns seeds owner ∧
      PhaseSeedScheduler.elapsed runtime leaks (originalCoordinate owner)
        execution.environmentRecall[index].beforeView = originalClock index := by
  classical
  let entry := execution.environmentRecall[index]
  have recorded : execution.environmentRecall = execution.environmentRecall.take index ++
      entry :: execution.environmentRecall.drop (index + 1) := by
    rw [List.getElem_cons_drop bounded, List.take_append_drop]
  obtain ⟨used, before, _within, ⟨beforeTrace⟩, _supported, recalled, viewed⟩ :=
    menu.recorded_environment_prefix initial horizon (family seeds) remaining execution trace
      (execution.environmentRecall.take index) entry
        (execution.environmentRecall.drop (index + 1)) recorded
  have raw := menu.toRawTrace initial horizon (family seeds) beforeTrace
  have valid := raw_native_valid (family seeds) _ raw
  have requested := callback.2
  change PhaseRuntimeState.requests entry.beforeView.application owner (originalCoordinate owner)
    at requested
  rw [viewed] at requested
  change PhaseRuntimeState.requests before.application.publicView owner (originalCoordinate owner)
    at requested
  have request := (before.application.requests_publicView valid owner (originalCoordinate owner)).mp
    requested
  have original : before.application.attempt = originalAttempt := request.1.symm
  have count : before.environmentRecall.length = index := by
    rw [recalled, List.length_take, Nat.min_eq_left (Nat.le_of_lt bounded)]
  have readyOwner : ready owner (bindingEvent owner) (before.observeEnvironment app) = true := by
    apply decide_eq_true
    change PhaseRuntimeState.requests before.application.publicView owner
      ⟨before.application.attempt, bindingEvent owner⟩
    rw [original]
    exact requested
  have commands := family_commands seeds _ (menu.toRawTrace initial horizon (family seeds) trace)
  rw [recorded] at commands
  have parts := (app.commandConsistentFrom_append choose seeds []
    (execution.environmentRecall.take index)
      (entry :: execution.environmentRecall.drop (index + 1))).mp commands
  have selected : choose seeds before.environmentRecall (before.observeEnvironment app) =
      .activate owner := by
    have chosen := parts.2.1
    rw [callback.1] at chosen
    simpa only [List.nil_append, ← recalled, viewed] using chosen
  rw [choose_original seeds _ _ original] at selected
  have turn := (original_command_activation seeds owner before.environmentRecall.length
    before.environmentRecall (before.observeEnvironment app) readyOwner).mp selected
  rw [count] at turn
  have stamp := original_timer (family seeds) _ raw original owner request.2.2.1.1
  change before.application.current.native.activatedAt (bindingEvent owner) = some 0 at stamp
  have elapsedEq : PhaseSeedScheduler.elapsed runtime leaks (originalCoordinate owner)
      entry.beforeView = originalClock index := by
    rw [viewed]
    change before.application.current.native.clock -
      (before.application.current.native.activatedAt (bindingEvent owner)).getD
        before.application.current.native.clock = originalClock index
    rw [stamp, Option.getD_some, Nat.sub_zero, original_clock_index seeds _ raw original, count]
  exact ⟨turn, elapsedEq⟩

/-- Every actual original callback at its seed-selected late clock lies before
that envelope's selected include in the retained environment history. -/
theorem original_eligible_callback_before_include (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (index : Nat) (bounded : index < execution.environmentRecall.length)
    (callback : PhaseSeedScheduler.callback runtime leaks (originalCoordinate owner) owner
      execution.environmentRecall[index])
    (eligible : PhaseSeedScheduler.elapsed runtime leaks (originalCoordinate owner)
      execution.environmentRecall[index].beforeView =
        lateClock (seeds.2 owner)) :
    index < lateIncludePosition seeds owner := by
  obtain ⟨turn, elapsedEq⟩ := original_recorded_callback_clock menu seeds remaining execution trace
    owner index bounded callback
  exact eligible_turn_before_include owner (seeds.1.symm owner) (seeds.2 owner) index turn
    (elapsedEq.symm.trans eligible)

private theorem zero_turn_before_three (owner rank : Player) (good : Bool) (index : Nat)
    (turn : index ∈ [owner.val, (if good then 5 else 11) + rank.val, 18 + rank.val])
    (clock : originalClock index = 0) : index < 3 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at turn
  rcases turn with rfl | rfl | rfl
  all_goals fin_cases owner <;> fin_cases rank <;> cases good
  all_goals norm_num [originalClock, originalClockFrom, originalTick] at clock
  all_goals norm_num

/-- A retained original callback at clock zero is one of the three initial
commands, including when read from a later archived or exhausted endpoint. -/
theorem original_clock_zero_callback_before_three (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (index : Nat) (bounded : index < execution.environmentRecall.length)
    (callback : PhaseSeedScheduler.callback runtime leaks (originalCoordinate owner) owner
      execution.environmentRecall[index])
    (zero : PhaseSeedScheduler.elapsed runtime leaks (originalCoordinate owner)
      execution.environmentRecall[index].beforeView = 0) : index < 3 := by
  obtain ⟨turn, elapsedEq⟩ := original_recorded_callback_clock menu seeds remaining execution trace
    owner index bounded callback
  exact zero_turn_before_three owner (seeds.1.symm owner) (seeds.2 owner) index turn
    (elapsedEq.symm.trans zero)
end Vegas.Examples.CommitSeedBroadcast
