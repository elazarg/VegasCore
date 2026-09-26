/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist

/-! # Lower bounds through stochastic execution

Multiplicative lower bounds on each compiled step compose along complete
executions. The larger kernel is unrestricted away from embedded source states;
it can reveal information and support arbitrary responses after a departure.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {Source Target : Type*} [Finite Target]

/-- Pointwise probability domination bounds every nonnegative expectation. -/
theorem mul_expect_le_of_prob_le (source target : FinDist Target) (factor : ℝ)
    (lower : ∀ value, factor * source.prob value ≤ target.prob value)
    (utility : Target → ℝ) (nonnegative : ∀ value, 0 ≤ utility value) :
    factor * source.expect utility ≤ target.expect utility := by
  classical
  let _ := Fintype.ofFinite Target
  rw [expect_eq_sum, expect_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro value _
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (lower value) (nonnegative value)

/-- A lower bound on the current law and a lower bound on the next-step kernel
multiply. The embedding need not be surjective or even injective for this law. -/
theorem bind_prob_domination (source : FinDist Source) (target : FinDist Target)
    (embed : Source → Target) (sourceStep : Source → FinDist Source)
    (targetStep : Target → FinDist Target) (initialFactor stepFactor : ℝ)
    (initialNonnegative : 0 ≤ initialFactor)
    (initialLower : ∀ value, initialFactor * (source.map embed).prob value ≤ target.prob value)
    (stepLower : ∀ state value,
      stepFactor * ((sourceStep state).map embed).prob value ≤
        (targetStep (embed state)).prob value) (value : Target) :
    (initialFactor * stepFactor) * ((source.bind sourceStep).map embed).prob value ≤
      (target.bind targetStep).prob value := by
  rw [map_bind, prob_bind, prob_bind]
  calc
    _ = initialFactor * source.expect
        (fun state => stepFactor * ((sourceStep state).map embed).prob value) := by
      rw [show (fun state => stepFactor * ((sourceStep state).map embed).prob value) =
          (fun state => ((sourceStep state).map embed).prob value * stepFactor) by
            funext state; ring, expect_mul_const]
      ring
    _ ≤ initialFactor * source.expect (fun state => (targetStep (embed state)).prob value) :=
      mul_le_mul_of_nonneg_left (expect_mono (fun state _ => stepLower state value))
        initialNonnegative
    _ = initialFactor * (source.map embed).expect
        (fun state => (targetStep state).prob value) := by rw [expect_map]
    _ ≤ target.expect (fun state => (targetStep state).prob value) :=
      mul_expect_le_of_prob_le (source.map embed) target initialFactor initialLower
        _ (fun state => prob_nonneg (targetStep state) value)

/-- Iterated one-step domination preserves every source outcome with at least
the product of the step factors. Other target histories remain unrestricted. -/
theorem iterate_prob_domination (initial : FinDist Source) (embed : Source → Target)
    (sourceStep : Source → FinDist Source) (targetStep : Target → FinDist Target)
    (factor : ℝ) (nonnegative : 0 ≤ factor)
    (stepLower : ∀ state value,
      factor * ((sourceStep state).map embed).prob value ≤
        (targetStep (embed state)).prob value) (steps : Nat) (value : Target) :
    factor ^ steps *
        (((fun law => law.bind sourceStep)^[steps] initial).map embed).prob value ≤
      ((fun law => law.bind targetStep)^[steps] (initial.map embed)).prob value := by
  induction steps generalizing value with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
      exact bind_prob_domination
        ((fun law => law.bind sourceStep)^[steps] initial)
        ((fun law => law.bind targetStep)^[steps] (initial.map embed))
        embed sourceStep targetStep (factor ^ steps) factor (pow_nonneg nonnegative _)
        (fun value => ih value) stepLower value

end GameTheory.Math.Probability.FinDist
