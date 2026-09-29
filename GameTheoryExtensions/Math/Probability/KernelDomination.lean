/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Lower bounds through stochastic execution

Multiplicative lower bounds on each compiled step compose along complete
executions. The larger kernel is unrestricted away from embedded source states;
it can reveal information and support arbitrary responses after a departure.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {Source Target : Type*} [Finite Target]

/-- Pointwise probability domination bounds every nonnegative expectation. -/
theorem mul_expect_le_of_prob_le (source target : PMF Target) (factor : ℝ)
    (lower : ∀ value, factor * (source value).toReal ≤ (target value).toReal)
    (utility : Target → ℝ) (nonnegative : ∀ value, 0 ≤ utility value) :
    factor * expect source utility ≤ expect target utility := by
  classical
  let _ := Fintype.ofFinite Target
  rw [expect_eq_sum, expect_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro value _
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (lower value) (nonnegative value)

/-- A lower bound on the current law and a lower bound on the next-step kernel
multiply. The embedding need not be surjective or even injective for this law. -/
theorem bind_prob_domination (source : PMF Source) (target : PMF Target)
    (embed : Source → Target) (sourceStep : Source → PMF Source)
    (targetStep : Target → PMF Target) (initialFactor stepFactor : ℝ)
    (initialNonnegative : 0 ≤ initialFactor)
    (initialLower : ∀ value,
        initialFactor * ((source.map embed) value).toReal ≤ (target value).toReal)
    (stepLower : ∀ state value,
      stepFactor * (((sourceStep state).map embed) value).toReal ≤
        ((targetStep (embed state)) value).toReal) (value : Target) :
    (initialFactor * stepFactor) * (((source.bind sourceStep).map embed) value).toReal ≤
      ((target.bind targetStep) value).toReal := by
  rw [PMF.map_bind, toReal_bind_apply, toReal_bind_apply]
  calc
    _ = initialFactor * expect source
        (fun state => stepFactor * (((sourceStep state).map embed) value).toReal) := by
      rw [expect_const_mul]
      ring
    _ ≤ initialFactor * expect source (fun state => ((targetStep (embed state)) value).toReal) :=
      mul_le_mul_of_nonneg_left (expect_mono (fun state _ => stepLower state value)
        (payoffIntegrable_of_bounded _ _ (C := |stepFactor|) fun state => by
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_of_le_one_right (abs_nonneg _) (pmf_toReal_apply_le_one _ _))
        (payoffIntegrable_toReal_apply source (fun state => targetStep (embed state)) value))
        initialNonnegative
    _ = initialFactor * expect (source.map embed)
        (fun state => ((targetStep state) value).toReal) := by rw [expect_map]; rfl
    _ ≤ expect target (fun state => ((targetStep state) value).toReal) :=
      mul_expect_le_of_prob_le (source.map embed) target initialFactor initialLower
        _ (fun _ => ENNReal.toReal_nonneg)

/-- Iterated one-step domination preserves every source outcome with at least
the product of the step factors. Other target histories remain unrestricted. -/
theorem iterate_prob_domination (initial : PMF Source) (embed : Source → Target)
    (sourceStep : Source → PMF Source) (targetStep : Target → PMF Target)
    (factor : ℝ) (nonnegative : 0 ≤ factor)
    (stepLower : ∀ state value,
      factor * (((sourceStep state).map embed) value).toReal ≤
        ((targetStep (embed state)) value).toReal) (steps : Nat) (value : Target) :
    factor ^ steps *
        ((((fun law => law.bind sourceStep)^[steps] initial).map embed) value).toReal ≤
      (((fun law => law.bind targetStep)^[steps] (initial.map embed)) value).toReal := by
  induction steps generalizing value with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
      exact bind_prob_domination
        ((fun law => law.bind sourceStep)^[steps] initial)
        ((fun law => law.bind targetStep)^[steps] (initial.map embed))
        embed sourceStep targetStep (factor ^ steps) factor (pow_nonneg nonnegative _)
        (fun value => ih value) stepLower value

end PMF
