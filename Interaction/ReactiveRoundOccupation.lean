/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOccupationValue
import GameTheory.Math.Probability.ExpectationAlgebra

/-! # Occupation summed over actual environment-command indices -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (scheduler : app.Scheduler) (players : Principal → app.Policy)
  (reward : app.ProtocolState → ℝ)

/-- Expected reward at the actual next command/environment boundary. -/
def roundDecisionReward (remaining : Nat) (execution : app.Execution) : ℝ :=
  expect (scheduler execution.environmentRecall (execution.observeEnvironment app)) fun command =>
    expect (execution.environmentStep app command) fun active =>
      reward (some ⟨remaining, command.actor? app, active⟩)

/-- The next command/environment decision retains the reward bound. -/
theorem roundDecisionReward_abs_le {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ state, |reward state| ≤ bound) (remaining : Nat) (execution : app.Execution) :
    |app.roundDecisionReward scheduler reward remaining execution| ≤ bound := by
  apply expect_abs_le_of_bounded nonnegative
  intro command
  exact expect_abs_le_of_bounded nonnegative fun active => bounded _

/-- Separate the next actual decision reward from the occupation of later rounds. -/
theorem roundOccupation_succ {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ state, |reward state| ≤ bound) (remaining : Nat) (execution : app.Execution) :
    app.roundOccupation scheduler players reward (remaining + 1) execution =
      app.roundDecisionReward scheduler reward remaining execution +
        expect (app.round scheduler players execution)
          (app.roundOccupation scheduler players reward remaining) := by
  let rest := app.roundOccupation scheduler players reward remaining
  have restNonnegative : 0 ≤ (remaining : ℝ) * bound :=
    mul_nonneg (Nat.cast_nonneg _) nonnegative
  have restBounded : ∀ next, |rest next| ≤ (remaining : ℝ) * bound :=
    app.roundOccupation_abs_le scheduler players reward nonnegative bounded remaining
  have responseBounded (command : app.Command) (active : app.Execution) :
      |expect (app.resume players (command.actor? app) active) rest| ≤
        (remaining : ℝ) * bound := expect_abs_le_of_bounded restNonnegative restBounded
  have inner (command : app.Command) :
      expect (execution.environmentStep app command) (fun active =>
        reward (some ⟨remaining, command.actor? app, active⟩) +
          expect (app.resume players (command.actor? app) active) rest) =
        expect (execution.environmentStep app command)
          (fun active => reward (some ⟨remaining, command.actor? app, active⟩)) +
        expect (execution.environmentStep app command)
          (fun active => expect (app.resume players (command.actor? app) active) rest) :=
    expect_add (payoffIntegrable_of_bounded _ _ fun active => bounded _)
      (payoffIntegrable_of_bounded _ _ (responseBounded command))
  have decisionBounded (command : app.Command) :
      |expect (execution.environmentStep app command)
        (fun active => reward (some ⟨remaining, command.actor? app, active⟩))| ≤ bound :=
    expect_abs_le_of_bounded nonnegative fun active => bounded _
  have afterBounded (command : app.Command) :
      |expect (execution.environmentStep app command)
        (fun active => expect (app.resume players (command.actor? app) active) rest)| ≤
          (remaining : ℝ) * bound :=
    expect_abs_le_of_bounded restNonnegative (responseBounded command)
  change expect (scheduler execution.environmentRecall (execution.observeEnvironment app))
      (fun command => expect (execution.environmentStep app command) fun active =>
        reward (some ⟨remaining, command.actor? app, active⟩) +
          expect (app.resume players (command.actor? app) active) rest) =
    expect (scheduler execution.environmentRecall (execution.observeEnvironment app))
      (fun command => expect (execution.environmentStep app command)
        (fun active => reward (some ⟨remaining, command.actor? app, active⟩))) +
      expect (app.round scheduler players execution) rest
  simp_rw [inner]
  rw [expect_add (payoffIntegrable_of_bounded _ _ decisionBounded)
    (payoffIntegrable_of_bounded _ _ afterBounded)]
  congr 1
  symm
  unfold round
  rw [expect_bind_tower_bounded _ _ rest restBounded]
  apply expect_congr_on_support
  intro command _
  exact expect_bind_tower_bounded _ _ rest restBounded

/-- The exact occupation is the sum of genuine next-command rewards over
precisely the remaining environmental indices, with no terminal extra command. -/
theorem roundOccupation_eq_sum_decisions {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ state, |reward state| ≤ bound) (remaining : Nat) (execution : app.Execution) :
    app.roundOccupation scheduler players reward remaining execution =
      ∑ time : Fin remaining, expect (app.runRounds scheduler players time.val execution)
        (app.roundDecisionReward scheduler reward (remaining - time.val - 1)) := by
  induction remaining generalizing execution with
  | zero => simp only [roundOccupation, Finset.univ_eq_empty, Finset.sum_empty]
  | succ remaining ih =>
      rw [app.roundOccupation_succ scheduler players reward nonnegative bounded]
      have future : expect (app.round scheduler players execution)
          (app.roundOccupation scheduler players reward remaining) =
          ∑ time : Fin remaining,
            expect (app.runRounds scheduler players (time.val + 1) execution)
              (app.roundDecisionReward scheduler reward (remaining - time.val - 1)) := by
        calc
          _ = expect (app.round scheduler players execution) (fun next =>
              ∑ time : Fin remaining, expect (app.runRounds scheduler players time.val next)
                (app.roundDecisionReward scheduler reward (remaining - time.val - 1))) :=
            expect_congr_on_support fun next _ => ih next
          _ = ∑ time : Fin remaining, expect (app.round scheduler players execution)
              (fun next => expect (app.runRounds scheduler players time.val next)
                (app.roundDecisionReward scheduler reward (remaining - time.val - 1))) := by
            apply expect_sum
            intro time
            apply payoffIntegrable_of_bounded _ _ (C := bound)
            intro next
            exact expect_abs_le_of_bounded nonnegative
              (app.roundDecisionReward_abs_le scheduler reward nonnegative bounded _)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro time _
            exact (expect_bind_tower_bounded _ _ _
              (app.roundDecisionReward_abs_le scheduler reward nonnegative bounded _)).symm
      rw [future, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_cancel_right,
        Nat.add_sub_add_right, runRounds, expect_pure]

end Interaction.ReactiveApplication
