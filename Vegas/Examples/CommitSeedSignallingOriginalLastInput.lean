/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingLateBeliefs

/-! # The actual final original Alice callback has command position ten -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- A genuine original Alice input at clock three follows command nine,
under arbitrary raw responses and either original private seed. -/
theorem alice_original_clock_three_input_index (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (active : current.actor = some alice)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = 3) :
    current.execution.environmentRecall.length = 10 := by
  obtain ⟨_accounted, supported⟩ := rawMenu.roundSupported_uniform initial horizon
    (family seed) trace
  rw [active] at supported
  obtain ⟨count, before, command, position, reached, selected, actor, moved⟩ := supported
  have commandEq : command = (ReactiveApplication.Command.activate alice : app.Command) := by
    cases command <;> simp only [ReactiveApplication.Command.actor?, Option.some.injEq] at actor
    · exact congrArg ReactiveApplication.Command.activate actor
    all_goals cases actor
  subst command
  rw [completeActivation_law] at moved
  have executionEq := (PMF.mem_support_pure_iff _ _).mp moved
  have originalBefore : before.application.attempt = originalAttempt := by
    rw [executionEq] at original
    exact original
  have clockBefore : before.application.current.native.clock = 3 := by
    rw [executionEq] at clock
    exact clock
  obtain ⟨beforeTrace⟩ := rawMenu.trace_roundsFrom initial horizon (family seed)
    rawMenu.uniformResponses (by
      intro who past view action member
      exact (rawMenu.uniformResponses_support who past view action).mp member)
    count (by omega) before reached
  rw [family_apply, choose_original _ _ _ originalBefore] at selected
  have chosen : originalCommand seed before.environmentRecall.length before.environmentRecall
      (before.observeEnvironment app) = .activate alice :=
    ((PMF.mem_support_pure_iff _ _).mp selected).symm
  have bounded : before.environmentRecall.length < 22 := by
    by_contra late
    rw [originalCommand_bound _ _ _ _ (by omega)] at chosen
    cases chosen
  have turns := original_activation_positions seed _ _ _ alice bounded chosen
  have indexed := original_clock_index seed ⟨horizon - count, none, before⟩
    (rawMenu.toRawTrace initial horizon (family seed) beforeTrace) originalBefore
  have beforeIndex : before.environmentRecall.length = 9 := by
    have elapsed := indexed.symm.trans clockBefore
    rcases turns with turn | turn | turn | turn | turn | turn | turn | turn
    all_goals first
    | exact turn
    | norm_num [turn, originalClock, originalClockFrom, originalTick] at elapsed
  rw [executionEq]
  change (before.environmentRecall ++ [_]).length = 10
  rw [List.length_append, List.length_singleton, beforeIndex]

end Vegas.Examples.CommitSeedSignalling
