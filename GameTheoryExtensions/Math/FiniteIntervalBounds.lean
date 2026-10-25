/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Uniform bounds from finite intervals containing zero -/

namespace GameTheory.Math

/-- Every coordinate in an interval containing zero is bounded in absolute
value by the sum of the widths of a finite family of such intervals. -/
theorem abs_le_sum_interval_width {ι : Type*} [Fintype ι]
    (lower upper : ι → ℝ) (lower_nonpos : ∀ i, lower i ≤ 0)
    (upper_nonneg : ∀ i, 0 ≤ upper i) (i : ι) {value : ℝ}
    (within : value ∈ Set.Icc (lower i) (upper i)) :
    |value| ≤ ∑ j, (upper j - lower j) := by
  have own : |value| ≤ upper i - lower i :=
    abs_le.mpr ⟨by linarith [within.1, upper_nonneg i],
      by linarith [within.2, lower_nonpos i]⟩
  exact own.trans (Finset.single_le_sum
    (fun j _ => sub_nonneg.mpr ((lower_nonpos j).trans (upper_nonneg j))) (Finset.mem_univ i))

end GameTheory.Math
