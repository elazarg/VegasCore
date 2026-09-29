/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.Approximate

/-! # An optimal plan does not determine optimal restricted continuations

Both utility profiles select `a` in the full one-decision game. When a native
prefix leaves only `b` and `c` available, their best replies disagree. No
randomized continuation is optimal for both. A utility-independent compiler
cannot recover this missing ranking from the common source plan alone.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ContinuationMenus

open GameTheory GameTheory.Math.Probability

inductive Outcome where
  | a | b | c
  deriving DecidableEq, Fintype

abbrev source : GameForm Unit where
  sig := { Strategy := fun _ => PMF Outcome, Outcome := Outcome }
  play profile := profile ()

def remainingOutcome (choice : Bool) : Outcome := if choice then .b else .c

abbrev continuation : GameForm Unit where
  sig := { Strategy := fun _ => PMF Bool, Outcome := Outcome }
  play profile := (profile ()).map remainingOutcome

def utilityB : Outcome → Unit → ℝ
  | .a, _ => 3
  | .b, _ => 2
  | .c, _ => 1

def utilityC : Outcome → Unit → ℝ
  | .a, _ => 3
  | .b, _ => 1
  | .c, _ => 2

def sourcePlan : Profile source.sig := fun _ => PMF.pure .a

theorem sourcePlan_optimal_for_both :
    IsεNash source utilityB 0 sourcePlan ∧ IsεNash source utilityC 0 sourcePlan := by
  constructor <;> rw [isεNash_iff] <;> intro who replacement <;> cases who
  all_goals
    refine ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _, ?_⟩
    simp only [expectedUtility, source, Profile.update_same, sourcePlan, expect_pure,
      utilityB, utilityC, add_zero]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
    intro result _
    cases result <;> norm_num [utilityB, utilityC]

theorem continuation_utility_sum (profile : Profile continuation.sig) :
    expect (continuation.play profile) (fun outcome => utilityB outcome ()) +
      expect (continuation.play profile) (fun outcome => utilityC outcome ()) = 3 := by
  simp only [continuation, expect_map, Function.comp_def]
  rw [← expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  have values : (fun choice =>
      utilityB (remainingOutcome choice) () + utilityC (remainingOutcome choice) ()) =
      fun _ => (3 : ℝ) := by
    funext choice
    cases choice <;> norm_num [remainingOutcome, utilityB, utilityC]
  rw [values, expect_constant]

theorem no_common_optimal_continuation :
    ¬ ∃ profile : Profile continuation.sig,
      IsεNash continuation utilityB 0 profile ∧ IsεNash continuation utilityC 0 profile := by
  rintro ⟨profile, bestB, bestC⟩
  rw [isεNash_iff] at bestB bestC
  have prefersB := (bestB () (PMF.pure true)).2.2
  have prefersC := (bestC () (PMF.pure false)).2.2
  simp only [expectedUtility, continuation, Profile.update_same, PMF.pure_map,
    expect_pure, remainingOutcome, ite_true, utilityB, utilityC,
    add_zero] at prefersB prefersC
  have total := continuation_utility_sum profile
  simp only [continuation, expect_map, Function.comp_def] at total
  simp only [expect_map] at prefersB prefersC
  change (2 : ℝ) ≤ expect (profile ())
    (fun choice => utilityB (remainingOutcome choice) ()) at prefersB
  change (2 : ℝ) ≤ expect (profile ())
    (fun choice => utilityC (remainingOutcome choice) ()) at prefersC
  linarith

/-- Even randomized completion cannot preserve optimality for every utility
when it receives only the source plan and the restricted menu. -/
theorem no_utility_independent_completion :
    ¬ ∃ complete : PMF Outcome → PMF Bool,
      ∀ utility : Outcome → Unit → ℝ,
        IsεNash source utility 0 sourcePlan →
          IsεNash continuation utility 0 (fun _ => complete (sourcePlan ())) := by
  rintro ⟨complete, preserves⟩
  exact no_common_optimal_continuation
    ⟨fun _ => complete (sourcePlan ()),
      preserves utilityB sourcePlan_optimal_for_both.1,
      preserves utilityC sourcePlan_optimal_for_both.2⟩

end GameTheoryExtensionsTests.ContinuationMenus
