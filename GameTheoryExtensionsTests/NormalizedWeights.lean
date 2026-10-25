/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.SwapTransport
import GameTheoryExtensions.Math.Probability.NestedPosterior

/-! # Sharp finite normalization bounds and null-observation fallback -/

noncomputable section

namespace GameTheoryExtensionsTests.NormalizedWeights

open GameTheory.Math.Probability

private def base (point : Bool) : ℝ := if point then 0 else 1

private def added (point : Bool) : ℝ := if point then 3 else 0

/-- Disjoint added mass attains the improved contamination bound. -/
theorem contamination_attains_bound :
    (∑ point : Bool, |(base point + added point) / ∑ other : Bool, (base other + added other) -
      base point / ∑ other : Bool, base other|) = 2 * (3 : ℝ) / (1 + 3) := by
  norm_num [base, added, Fintype.sum_bool]

theorem contamination_bound :
    (∑ point : Bool, |(base point + added point) / ∑ other : Bool, (base other + added other) -
      base point / ∑ other : Bool, base other|) ≤ 3 / 2 := by
  have bound := sum_abs_div_sum_add_sub_div_sum_le (m := base) (s := added) (η := 3)
    (by intro point; cases point <;> norm_num [base])
    (by intro point; cases point <;> norm_num [added])
    (by norm_num [base, Fintype.sum_bool])
    (by norm_num [base, added, Fintype.sum_bool])
  norm_num at bound ⊢
  exact bound

/-- Centering uses equality of totals even for signed weights. -/
theorem signed_equal_mass_bound :
    |∑ point : Bool, (if point then (2 : ℝ) else -1) * (if point then 1 else 0) -
      ∑ point : Bool, (if point then (0 : ℝ) else 1) * (if point then 1 else 0)| ≤
      (∑ point : Bool, |(if point then (2 : ℝ) else -1) -
        (if point then (0 : ℝ) else 1)|) / 2 := by
  apply abs_sum_mul_sub_le_half_sum_abs
  · norm_num [Fintype.sum_bool]
  · intro point
    cases point <;> norm_num

/-- At an impossible observation the total posterior returns its input law. -/
theorem null_observation_fallback :
    fiberPosterior (PMF.pure true) (fun point : Bool => point) false = PMF.pure true := by
  apply fiberPosterior_of_not_mem_support
  simp

end GameTheoryExtensionsTests.NormalizedWeights
