/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketContentFloor
import Vegas.Game.OnePacketComponentSteps

/-! # The error of slot-trembled components

The full-menu tremble of a slot-trembled component has mass the cube of the
scale. Against the rest of the component, it is a vanishing share
(`Vegas.slotError`): a choice the main or alternative law gives mass one keeps at
least the scale times a fixed share (`Vegas.cube_le_slotError_of_one`), and a
choice the slot tier gives the uniform slot mass, with content at least the
floor, keeps at least the square of the scale over the number of slots
(`Vegas.cube_le_slotError_of_slot`). Along the tremble scale of a floor
sequence, the error vanishes (`Vegas.tendsto_slotError`).
-/

noncomputable section

namespace Vegas

open Filter

/-- The error of a slot-trembled component at a scale, a floor and a number of
slots. -/
def slotError (scale floor : ℝ) (slots : ℕ) : ℝ :=
  2 * scale * slots / floor + 2 * scale ^ 2

theorem slotError_nonneg {scale floor : ℝ} (nonnegative : 0 ≤ scale) (positive : 0 < floor)
    (slots : ℕ) : 0 ≤ slotError scale floor slots := by
  unfold slotError
  positivity

/-- **A choice of mass one.** If the main or alternative law gives a choice
mass one, its slot combination keeps the cube of the scale within the error. -/
theorem cube_le_slotError_of_one {scale floor : ℝ} (nonnegative : 0 ≤ scale)
    (small : scale ≤ 1 / 4) (positive : 0 < floor) (slots : ℕ) {main alternative slot : ℝ}
    (mainNonneg : 0 ≤ main) (alternativeNonneg : 0 ≤ alternative) (slotNonneg : 0 ≤ slot)
    (one : main = 1 ∨ alternative = 1) :
    scale ^ 3 ≤ slotError scale floor slots * 1 * slotCombination scale main alternative slot := by
  have share : scale * (1 / 2) ≤ slotCombination scale main alternative slot := by
    unfold slotCombination
    have cube : scale ^ 3 ≤ 1 / 64 := by
      calc scale ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ nonnegative small 3
        _ = 1 / 64 := by norm_num
    have square : scale ^ 2 ≤ 1 / 16 := by
      calc scale ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ nonnegative small 2
        _ = 1 / 16 := by norm_num
    have inner : scale ≤ scale * alternative + (1 - scale) * main := by
      rcases one with mainOne | alternativeOne
      · rw [mainOne]
        nlinarith
      · rw [alternativeOne]
        nlinarith
    have slotPart : 0 ≤ scale ^ 2 * slot := by positivity
    have outer : (15 / 16) * scale ≤
        (1 - scale ^ 2) * (scale * alternative + (1 - scale) * main) := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - scale ^ 2 by linarith) (sub_nonneg.mpr inner)]
    have total : (15 / 16) * scale ≤
        scale ^ 2 * slot + (1 - scale ^ 2) * (scale * alternative + (1 - scale) * main) := by
      linarith
    have totalNonneg : 0 ≤
        scale ^ 2 * slot + (1 - scale ^ 2) * (scale * alternative + (1 - scale) * main) := by
      linarith
    nlinarith [mul_nonneg (show 0 ≤ 1 / 64 - scale ^ 3 by linarith) totalNonneg]
  have errorBound : 2 * scale ^ 2 ≤ slotError scale floor slots := by
    unfold slotError
    have : 0 ≤ 2 * scale * slots / floor := by positivity
    linarith
  calc scale ^ 3 = 2 * scale ^ 2 * (scale * (1 / 2)) := by ring
    _ ≤ slotError scale floor slots * (scale * (1 / 2)) :=
        mul_le_mul_of_nonneg_right errorBound (by positivity)
    _ ≤ slotError scale floor slots * slotCombination scale main alternative slot :=
        mul_le_mul_of_nonneg_left share (slotError_nonneg nonnegative positive slots)
    _ = slotError scale floor slots * 1 * slotCombination scale main alternative slot := by ring

/-- **A slot-tier choice.** If the slot tier gives a choice the uniform slot
mass and its content is at least the floor, its slot combination keeps the cube
of the scale within the error. -/
theorem cube_le_slotError_of_slot {scale floor content : ℝ} (nonnegative : 0 ≤ scale)
    (small : scale ≤ 1 / 4) (positive : 0 < floor) (floored : floor ≤ content) {slots : ℕ}
    (slotsPos : 0 < slots) {main alternative : ℝ} (mainNonneg : 0 ≤ main)
    (alternativeNonneg : 0 ≤ alternative) :
    scale ^ 3 ≤ slotError scale floor slots * content *
      slotCombination scale main alternative (1 / slots) := by
  have slotsReal : (0 : ℝ) < slots := Nat.cast_pos.mpr slotsPos
  have share : scale ^ 2 / slots * (1 / 2) ≤
      slotCombination scale main alternative (1 / slots) := by
    unfold slotCombination
    have cube : scale ^ 3 ≤ 1 / 64 := by
      calc scale ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ nonnegative small 3
        _ = 1 / 64 := by norm_num
    have square : scale ^ 2 ≤ 1 / 16 := by
      calc scale ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ nonnegative small 2
        _ = 1 / 16 := by norm_num
    have rest : 0 ≤ (1 - scale ^ 2) * (scale * alternative + (1 - scale) * main) := by
      have complement : 0 ≤ 1 - scale := by linarith
      exact mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg nonnegative alternativeNonneg) (mul_nonneg complement mainNonneg))
    have slotTerm : scale ^ 2 * (1 / slots) = scale ^ 2 / slots := by ring
    have slotNonneg : 0 ≤ scale ^ 2 / slots := by positivity
    nlinarith
  have errorBound : 2 * scale * slots / floor ≤ slotError scale floor slots := by
    unfold slotError
    have : 0 ≤ 2 * scale ^ 2 := by positivity
    linarith
  have contentPos : 0 < content := lt_of_lt_of_le positive floored
  have combinationNonneg : 0 ≤ scale ^ 2 / slots * (1 / 2) := by positivity
  calc scale ^ 3 = 2 * scale * slots / floor * floor * (scale ^ 2 / slots * (1 / 2)) := by
        field_simp
    _ ≤ slotError scale floor slots * content * (scale ^ 2 / slots * (1 / 2)) := by
        apply mul_le_mul_of_nonneg_right _ combinationNonneg
        exact mul_le_mul errorBound floored positive.le
          (slotError_nonneg nonnegative positive slots)
    _ ≤ slotError scale floor slots * content *
        slotCombination scale main alternative (1 / slots) :=
        mul_le_mul_of_nonneg_left share
          (mul_nonneg (slotError_nonneg nonnegative positive slots) contentPos.le)

/-- **The error vanishes.** Along the tremble scale of a floor sequence, the
error of slot-trembled components vanishes. -/
theorem tendsto_slotError (floors : ℕ → ℝ) (positive : ∀ n, 0 < floors n)
    (le_one : ∀ n, floors n ≤ 1) (depth slots : ℕ) :
    Tendsto (fun n => slotError (trembleScale (floors n) depth n) (floors n) slots) atTop
      (nhds 0) := by
  have ratio := tendsto_trembleScale_div floors positive le_one (depth := depth)
  have scale := tendsto_trembleScale floors positive le_one (depth := depth)
  have first : Tendsto (fun n => 2 * (slots : ℝ) * (trembleScale (floors n) depth n / floors n))
      atTop (nhds (2 * slots * 0)) := ratio.const_mul _
  have second : Tendsto (fun n => 2 * trembleScale (floors n) depth n ^ 2) atTop
      (nhds (2 * 0 ^ 2)) := (scale.pow 2).const_mul _
  have sum := first.add second
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    at sum
  refine sum.congr fun n => ?_
  unfold slotError
  ring

end Vegas
