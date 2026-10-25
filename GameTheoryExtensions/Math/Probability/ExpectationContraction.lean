/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.ExpectationAlgebra

/-! # Absolute-error contraction under expectation

Expectation contracts mean absolute error. Integration guards are explicit;
none of the statements requires a finite outcome carrier or support.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- The absolute expected value is bounded by its mean absolute value. -/
theorem abs_expect_le_expect_abs {Outcome : Type*} (law : PMF Outcome)
    (value : Outcome → ℝ) (integrable : PayoffIntegrable law value) :
    |expect law value| ≤ expect law (fun outcome => |value outcome|) := by
  have summable : Summable (fun outcome => ‖(law outcome).toReal * value outcome‖) := by
    simpa only [PayoffIntegrable, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg] using integrable
  simpa only [expect, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg] using norm_tsum_le_tsum_norm summable

/-- Expected values differ by at most their mean absolute difference. -/
theorem abs_expect_sub_le_expect_abs_sub {Outcome : Type*} (law : PMF Outcome)
    (first second : Outcome → ℝ)
    (firstIntegrable : PayoffIntegrable law first)
    (secondIntegrable : PayoffIntegrable law second) :
    |expect law first - expect law second| ≤
      expect law (fun outcome => |first outcome - second outcome|) := by
  rw [← expect_sub firstIntegrable secondIntegrable]
  exact abs_expect_le_expect_abs law _ (payoffIntegrable_sub firstIntegrable secondIntegrable)

/-- A supported uniform error bounds the difference of two integrable values. -/
theorem abs_expect_sub_le_of_bound {Outcome : Type*} (law : PMF Outcome)
    (first second : Outcome → ℝ)
    (firstIntegrable : PayoffIntegrable law first)
    (secondIntegrable : PayoffIntegrable law second) (bound : ℝ)
    (near : ∀ outcome ∈ law.support, |first outcome - second outcome| ≤ bound) :
    |expect law first - expect law second| ≤ bound :=
  (abs_expect_sub_le_expect_abs_sub law first second firstIntegrable secondIntegrable).trans
    (expect_le_const law _ (payoffIntegrable_of_bounded_on_support law _
      (fun outcome supported => by simpa only [abs_abs] using near outcome supported)) bound near)

end GameTheory.Math.Probability
