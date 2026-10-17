/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPrePoll

/-! # Alice's actual state before her first late polling block -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

theorem original_callback_clock_before_alice_poll (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (early : current.execution.environmentRecall.length ≤ 4) :
    current.execution.application.current.native.clock = 0 := by
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

/-- The quiet initialized history cannot contain an already accepted Alice
binding before her late polling starts. -/
theorem alice_binding_unaccepted_before_poll (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (early : execution.environmentRecall.length ≤ 4)
    (empty : ∀ entry, execution.environmentRecall[2]? = some entry →
      ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ alice) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice execution := by
  intro accepted
  obtain ⟨message, emitted⟩ := original_binding_accepted_late_of_empty_snapshot seed remaining
    execution trace alice empty accepted
  obtain ⟨before, prior, retained, active, original, clock⟩ :=
    original_emission_callback seed remaining execution trace alice _ message emitted
  have pastPrefix := tracePrefix_environment_prefix seed before ⟨remaining, none, execution⟩
    prior trace retained
  have bounded : before.execution.environmentRecall.length ≤ 4 :=
    pastPrefix.length_le.trans early
  have tooEarly := original_callback_clock_before_alice_poll seed before
    (rawMenu.toRawTrace initial horizon (family seed) prior) alice active original bounded
  rw [clock] at tooEarly
  have late : 2 ≤ lateClock alice (seed.2 (originalAddress alice)) := by
    cases seed.2 (originalAddress alice) <;> decide
  omega

end Vegas.Examples.CommitSeedSignalling
