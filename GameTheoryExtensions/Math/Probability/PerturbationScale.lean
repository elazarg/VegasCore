/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Positive perturbations below a conditional-error bound

A positive perturbation can be chosen below a prescribed scale while its
weighted ratio to an arbitrary positive denominator remains below that scale.
The denominator need not be bounded above or converge along a sequence.
-/

namespace GameTheory.Math.Probability

/-- Choose a strictly positive rate whose absolute size and normalized weighted
size are both bounded by the given positive scale. -/
theorem exists_positive_rate_with_ratio_bound (scale denominator coefficient : ℝ)
    (scalePositive : 0 < scale) (denominatorPositive : 0 < denominator)
    (coefficientNonnegative : 0 ≤ coefficient) :
    ∃ rate : ℝ, 0 < rate ∧ rate ≤ scale ∧ coefficient * rate / denominator ≤ scale := by
  have divisorPositive : 0 < coefficient + 1 := by linarith
  let rate := min scale (scale * denominator / (coefficient + 1))
  have ratePositive : 0 < rate :=
    lt_min scalePositive (div_pos (mul_pos scalePositive denominatorPositive) divisorPositive)
  have rateBounded : rate ≤ scale := min_le_left _ _
  have productBound : rate * (coefficient + 1) ≤ scale * denominator :=
    (le_div_iff₀ divisorPositive).mp (min_le_right _ _)
  refine ⟨rate, ratePositive, rateBounded, ?_⟩
  apply (div_le_iff₀ denominatorPositive).mpr
  nlinarith [ratePositive.le]

end GameTheory.Math.Probability
