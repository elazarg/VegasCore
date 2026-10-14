/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import GameTheory.Math.Probability.ExpectationComposition

/-! # Expected occupation of active runtime controls

The numeric value sums rewards at actual environment decisions, before the
optional owner response. Scheduler rounds retain their ordinary evaluator.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (scheduler : app.Scheduler) (players : Principal → app.Policy)
  (reward : app.ProtocolState → ℝ)

/-- Expected active-control reward through the remaining actual scheduler rounds. -/
def roundOccupation : Nat → app.Execution → ℝ
  | 0, _ => 0
  | remaining + 1, execution =>
      expect (scheduler execution.environmentRecall (execution.observeEnvironment app))
        fun command => expect (execution.environmentStep app command) fun active =>
          reward (some ⟨remaining, command.actor? app, active⟩) +
            expect (app.resume players (command.actor? app) active)
              (roundOccupation remaining)

/-- The same future occupation, including an owner decision already in progress. -/
def controlOccupation (initial : PMF app.State) (horizon : Nat) : app.ProtocolState → ℝ
  | none => expect initial fun state => app.roundOccupation scheduler players reward horizon
      (Execution.initial app state)
  | some current => reward (some current) +
      expect (app.resume players current.actor current.execution)
        (app.roundOccupation scheduler players reward current.remaining)

/-- Each remaining scheduler round contributes at most one bounded reward. -/
theorem roundOccupation_abs_le {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ state, |reward state| ≤ bound) (remaining : Nat) (execution : app.Execution) :
    |app.roundOccupation scheduler players reward remaining execution| ≤ remaining * bound := by
  induction remaining generalizing execution with
  | zero => simp only [roundOccupation, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ remaining ih =>
      have restBound : 0 ≤ (remaining : ℝ) * bound := mul_nonneg (Nat.cast_nonneg _) nonnegative
      have totalBound : 0 ≤ bound + (remaining : ℝ) * bound := add_nonneg nonnegative restBound
      have current : |app.roundOccupation scheduler players reward (remaining + 1) execution| ≤
          bound + (remaining : ℝ) * bound := by
        unfold roundOccupation
        apply expect_abs_le_of_bounded totalBound
        intro command
        apply expect_abs_le_of_bounded totalBound
        intro active
        exact (abs_add_le _ _).trans (add_le_add (bounded _)
          (expect_abs_le_of_bounded restBound (ih)))
      simpa only [roundOccupation, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        add_comm] using current

/-- At idle control the current reward vanishes and only future rounds remain. -/
theorem controlOccupation_idle (initial : PMF app.State) (horizon remaining : Nat)
    (execution : app.Execution)
    (idle : ∀ remaining execution, reward (some ⟨remaining, none, execution⟩) = 0) :
    app.controlOccupation scheduler players reward initial horizon
        (some ⟨remaining, none, execution⟩) =
      app.roundOccupation scheduler players reward remaining execution := by
  simp only [controlOccupation, idle, resume, expect_pure, zero_add]

/-- A current active control adds at most one reward to the remaining rounds. -/
theorem controlOccupation_abs_le {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ state, |reward state| ≤ bound) (initial : PMF app.State) (horizon : Nat)
    (current : app.Control) :
    |app.controlOccupation scheduler players reward initial horizon (some current)| ≤
      ((current.remaining : ℝ) + 1) * bound := by
  have restBound : 0 ≤ (current.remaining : ℝ) * bound :=
    mul_nonneg (Nat.cast_nonneg _) nonnegative
  calc
    _ ≤ |reward (some current)| +
        |expect (app.resume players current.actor current.execution)
          (app.roundOccupation scheduler players reward current.remaining)| := abs_add_le _ _
    _ ≤ bound + current.remaining * bound := add_le_add (bounded _)
      (expect_abs_le_of_bounded restBound fun execution =>
        app.roundOccupation_abs_le scheduler players reward nonnegative bounded _ execution)
    _ = _ := by ring

/-- The occupation potential vanishes at every terminal control. -/
theorem controlOccupation_terminal (initial : PMF app.State) (horizon : Nat)
    (idle : ∀ remaining execution, reward (some ⟨remaining, none, execution⟩) = 0)
    (state : app.ProtocolState) (ended : app.terminal state) :
    app.controlOccupation scheduler players reward initial horizon state = 0 := by
  cases state with
  | none => exact ended.elim
  | some current =>
      rcases current with ⟨remaining, actor, execution⟩
      rcases ended with ⟨rfl, rfl⟩
      rw [app.controlOccupation_idle scheduler players reward initial horizon 0 execution idle]
      rfl

end Interaction.ReactiveApplication
