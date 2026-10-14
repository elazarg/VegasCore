/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSlotError

/-! # The counterpart ratio is a power of the floor below the scale

At a tremble scale `s` below a floor `f ≤ 1`, the slot error is at most a
constant times `s / f` (`Vegas.slotError_le_div`). The comparison factor of a
counterpart, the largest of one, the inverse initial floor, the inverse content
floor and the response ratio, is then at most a constant over `f`, so the
counterpart ratio, the slot error times the error factor times that factor to a
power, is at most a constant times `s / f` to one more power
(`Vegas.counterpartRatio_le`).
-/

namespace Vegas

/-- **The slot error is at most a constant times the scale over the floor.** -/
theorem slotError_le_div {scale floor : ℝ} (scalePos : 0 < scale) (scaleLe : scale ≤ 1)
    (floorPos : 0 < floor) (floorLe : floor ≤ 1) (slots : ℕ) :
    slotError scale floor slots ≤ (2 * slots + 2) * (scale / floor) := by
  unfold slotError
  have square : scale ^ 2 ≤ scale / floor := by
    rw [le_div_iff₀ floorPos]
    nlinarith
  have rewrite : 2 * scale * slots / floor = 2 * slots * (scale / floor) := by ring
  rw [rewrite]
  nlinarith

/-- **The counterpart ratio.** At a tremble scale `scale` below a floor
`floor ≤ 1` at most the content floor `content`, with initial floor `initial`
and a slot error and factorization error `error` at most one, the slot error
times one plus the error times the comparison factor to the power `power` is at
most a constant times the scale over the floor to the power `power + 1`. -/
theorem counterpartRatio_le {scale floor content initial error : ℝ} (scalePos : 0 < scale)
    (scaleLe : scale ≤ 1) (floorPos : 0 < floor) (floorLe : floor ≤ 1)
    (floorContent : floor ≤ content)
    (initialPos : 0 < initial) (slots : ℕ) (errorNonneg : 0 ≤ error) (errorLe : error ≤ 1)
    (slotErrorLe : slotError scale floor slots ≤ 1) (power : ℕ) :
    slotError scale floor slots * (1 + error) *
        max 1 (max (max (1 / initial) (1 / content))
          ((1 / floor + slotError scale floor slots) * (1 + error))) ^ power ≤
      2 * (2 * slots + 2) * max (1 / initial) 4 ^ power * (scale / floor ^ (power + 1)) := by
  set bound := max (1 / initial) 4 with boundEq
  have boundPos : 0 < bound := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have inverseFloor : 1 ≤ 1 / floor := by rw [le_div_iff₀ floorPos]; linarith
  have slotNonneg : 0 ≤ slotError scale floor slots := slotError_nonneg scalePos.le floorPos _
  have factorLe : max 1 (max (max (1 / initial) (1 / content))
      ((1 / floor + slotError scale floor slots) * (1 + error))) ≤ bound / floor := by
    have overFloor : ∀ {x : ℝ}, x ≤ bound → x ≤ bound / floor := fun {x} le => by
      rw [le_div_iff₀ floorPos]
      have : 0 ≤ bound := boundPos.le
      rcases le_or_gt x 0 with negative | positive
      · nlinarith
      · nlinarith
    refine max_le (overFloor ((by norm_num : (1 : ℝ) ≤ 4).trans (le_max_right _ _)))
      (max_le (max_le (overFloor (le_max_left _ _)) ?_) ?_)
    · calc 1 / content ≤ 1 / floor := one_div_le_one_div_of_le floorPos floorContent
        _ ≤ bound / floor := by
          apply div_le_div_of_nonneg_right _ floorPos.le
          exact (by norm_num : (1 : ℝ) ≤ 4).trans (le_max_right _ _)
    · calc (1 / floor + slotError scale floor slots) * (1 + error) ≤ (2 / floor) * 2 := by
            apply mul_le_mul _ (by linarith) (by linarith) (by positivity)
            have : slotError scale floor slots ≤ 1 / floor := slotErrorLe.trans inverseFloor
            rw [show (2 : ℝ) / floor = 1 / floor + 1 / floor by ring]
            linarith
        _ = 4 / floor := by ring
        _ ≤ bound / floor := div_le_div_of_nonneg_right (le_max_right _ _) floorPos.le
  have factorNonneg : 0 ≤ max 1 (max (max (1 / initial) (1 / content))
      ((1 / floor + slotError scale floor slots) * (1 + error))) :=
    le_trans zero_le_one (le_max_left _ _)
  have powerLe := pow_le_pow_left₀ factorNonneg factorLe power
  have slotLe := slotError_le_div scalePos scaleLe floorPos floorLe slots
  have powerNonneg : 0 ≤ (bound / floor) ^ power := pow_nonneg (by positivity) _
  calc slotError scale floor slots * (1 + error) *
        max 1 (max (max (1 / initial) (1 / content))
          ((1 / floor + slotError scale floor slots) * (1 + error))) ^ power
      ≤ ((2 * slots + 2) * (scale / floor)) * 2 * (bound / floor) ^ power := by
        apply mul_le_mul _ powerLe (pow_nonneg factorNonneg _) (by positivity)
        exact mul_le_mul slotLe (by linarith) (by linarith) (by positivity)
    _ = 2 * (2 * slots + 2) * bound ^ power * (scale / floor ^ (power + 1)) := by
        rw [div_pow, pow_succ]
        field_simp

end Vegas
