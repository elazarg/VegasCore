/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.Support

/-! # Reflection of nested fibers with equal probability mass -/

noncomputable section

namespace GameTheory.Math.Probability

/-- An inclusion between supported fibers becomes an equality when their finite
marginal atom masses agree. A positive crossed atom would make the inclusion strict. -/
theorem fiber_reflection_of_equal_map_mass {Source First Second : Type*}
    (law : PMF Source) (first : Source → First) (second : Source → Second)
    (left : First) (right : Second)
    (forward : ∀ value ∈ law.support, second value = right → first value = left)
    (mass : (law.map first) left = (law.map second) right)
    (value : Source) (supported : value ∈ law.support) (same : first value = left) :
    second value = right := by
  classical
  by_contra different
  have strict : (law.map second) right < (law.map first) left := by
    rw [PMF.map_apply, PMF.map_apply]
    apply ENNReal.tsum_lt_tsum (i := value)
      (by simpa only [PMF.map_apply] using (law.map second).apply_ne_top right)
    · intro other
      by_cases present : other ∈ law.support
      · by_cases named : right = second other
        · have mapped := forward other present named.symm
          simp only [named, mapped, ite_true, le_refl]
        · simp only [named, ite_false, zero_le]
      · have zero : law other = 0 := not_ne_iff.mp ((law.mem_support_iff other).not.mp present)
        simp only [zero, ite_self, le_refl]
    · simpa only [same, eq_self_iff_true, ite_true, ite_false, Ne.symm different] using
        pos_iff_ne_zero.mpr ((law.mem_support_iff value).mp supported)
  exact (ne_of_lt strict) mass.symm

end GameTheory.Math.Probability
