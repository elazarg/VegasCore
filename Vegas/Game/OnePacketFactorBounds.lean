/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketUnifiedMasses
import Vegas.Game.OnePacketSlotError

/-! # Bounds on step factors

Every factor read from late-delivery keys lies in the unit interval
(`Vegas.honestFactor_mem`, `Vegas.lateOptionFactor_mem`, `Vegas.slotTierFactor_mem`,
`Vegas.silenceFactor_mem`), and the cube of the scale stays within the error
whenever the slot factor is at least the uniform slot mass
(`Vegas.cube_le_slotError_of_slot_ge`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

/-- The slot combination is monotone in the slot factor. -/
theorem slotCombination_mono_slot {scale main alternative slot slot' : ℝ}
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (le : slot ≤ slot') :
    slotCombination scale main alternative slot ≤ slotCombination scale main alternative slot' := by
  unfold slotCombination
  have cube : 0 ≤ 1 - scale ^ 3 := by
    have := pow_le_one₀ nonnegative le_one (n := 3)
    linarith
  apply mul_le_mul_of_nonneg_left _ cube
  have := mul_le_mul_of_nonneg_left le (sq_nonneg scale)
  linarith

/-- **A slot-tier choice, at least uniformly.** If the slot tier gives a choice
at least the uniform slot mass and its content is at least the floor, its slot
combination keeps the cube of the scale within the error. -/
theorem cube_le_slotError_of_slot_ge {scale floor content : ℝ} (nonnegative : 0 ≤ scale)
    (small : scale ≤ 1 / 4) (positive : 0 < floor) (floored : floor ≤ content) {slots : ℕ}
    (slotsPos : 0 < slots) {main alternative slot : ℝ} (mainNonneg : 0 ≤ main)
    (alternativeNonneg : 0 ≤ alternative) (uniform : 1 / (slots : ℝ) ≤ slot) :
    scale ^ 3 ≤ slotError scale floor slots * content *
      slotCombination scale main alternative slot :=
  (cube_le_slotError_of_slot nonnegative small positive floored slotsPos mainNonneg
    alternativeNonneg).trans
    (mul_le_mul_of_nonneg_left (slotCombination_mono_slot nonnegative (by linarith) uniform)
      (mul_nonneg (slotError_nonneg nonnegative positive slots)
        (positive.le.trans floored)))

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

theorem silenceFactor_mem (after : LateKey setup runtime leaks) :
    0 ≤ silenceFactor (runtime := runtime) after ∧ silenceFactor (runtime := runtime) after ≤ 1 :=
      by
  unfold silenceFactor
  split <;> norm_num

theorem transmitFactor_mem (after : LateKey setup runtime leaks) :
    0 ≤ transmitFactor (runtime := runtime) after ∧ transmitFactor (runtime := runtime) after ≤ 1
      := by
  unfold transmitFactor
  have := silenceFactor_mem (runtime := runtime) after
  constructor <;> linarith

theorem pendingBindingHonestFactor_mem (before after : LateKey setup runtime leaks) :
    0 ≤ pendingBindingHonestFactor (runtime := runtime) before after ∧ pendingBindingHonestFactor
      (runtime := runtime) before after ≤ 1 := by
  unfold pendingBindingHonestFactor
  split
  · split <;> norm_num
  · norm_num

theorem honestFactor_mem (before after : LateKey setup runtime leaks) :
    0 ≤ honestFactor (runtime := runtime) before after ∧ honestFactor (runtime := runtime) before
      after ≤ 1 := by
  unfold honestFactor
  split
  · norm_num
  · split
    · exact pendingBindingHonestFactor_mem (runtime := runtime) before after
    · exact transmitFactor_mem (runtime := runtime) after

variable (bounds : MessageBounds (graph setup))

theorem pendingBindingSlotFactor_mem (before after : LateKey setup runtime leaks)
    (event : (graph setup).EventId) :
    0 ≤ pendingBindingSlotFactor (runtime := runtime) bounds before after event ∧
      pendingBindingSlotFactor (runtime := runtime) bounds before after event ≤ 1 := by
  classical
  have positive : (0 : ℝ) < (trembleSlots setup bounds).card :=
    Nat.cast_pos.mpr (trembleSlots_nonempty setup bounds).card_pos
  unfold pendingBindingSlotFactor
  split
  · refine ⟨by positivity, ?_⟩
    rw [div_le_one positive]
    exact_mod_cast Finset.card_filter_le _ _
  · refine ⟨by positivity, ?_⟩
    rw [div_le_one positive]
    exact_mod_cast (trembleSlots_nonempty setup bounds).card_pos

theorem slotTierFactor_mem (before after : LateKey setup runtime leaks) :
    0 ≤ slotTierFactor (runtime := runtime) bounds before after ∧ slotTierFactor (runtime :=
      runtime) bounds before after ≤ 1 := by
  unfold slotTierFactor
  split
  · norm_num
  · split
    · exact pendingBindingSlotFactor_mem (runtime := runtime) bounds before after _
    · exact transmitFactor_mem (runtime := runtime) after

theorem lateOptionFactor_mem {slots : Nat} (before after : LateKey setup runtime leaks)
    (option : LateOption slots) :
    0 ≤ lateOptionFactor (runtime := runtime) bounds before after option ∧
      lateOptionFactor (runtime := runtime) bounds before after option ≤ 1 := by
  unfold lateOptionFactor
  split
  · exact silenceFactor_mem (runtime := runtime) after
  · split
    · exact silenceFactor_mem (runtime := runtime) after
    · split
      · split
        · split <;> norm_num
        · split <;> norm_num
      · exact transmitFactor_mem (runtime := runtime) after

end Vegas
