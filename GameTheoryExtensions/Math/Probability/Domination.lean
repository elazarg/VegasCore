/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.Domination
import GameTheory.Math.Probability.Mixture
import Mathlib.Tactic.Linarith

/-! # Atom domination through pushforwards and mixtures -/

noncomputable section

namespace GameTheory.Math.Probability

/-- A mixture retains its right component with its original weight. -/
theorem mix_retains_right {α : Type*} (weight : Set.Icc (0 : ℝ) 1)
    (extra retained : PMF α) (value : α) :
    (1 - weight.val) * (retained value).toReal ≤
      (mix weight.val weight.property.1 weight.property.2 extra retained value).toReal := by
  rw [mix_apply_toReal]
  exact le_add_of_nonneg_left (mul_nonneg weight.property.1 ENNReal.toReal_nonneg)

/-- Pushforward preserves a common pointwise mass lower bound. -/
theorem map_prob_domination {α β : Type*} (source target : PMF α)
    (factor : ℝ) (lower : ∀ value, factor * (source value).toReal ≤ (target value).toReal)
    (encode : α → β) (value : β) :
    factor * ((source.map encode) value).toReal ≤ ((target.map encode) value).toReal := by
  exact prob_bind_ge_mul source target factor lower (fun item => PMF.pure (encode item)) value

/-- A common mixture preserves a shared pointwise mass lower bound. -/
theorem mix_prob_domination {α : Type*} (weight : Set.Icc (0 : ℝ) 1)
    (firstSource firstTarget secondSource secondTarget : PMF α) (factor : ℝ)
    (first : ∀ value, factor * (firstSource value).toReal ≤ (firstTarget value).toReal)
    (second : ∀ value, factor * (secondSource value).toReal ≤ (secondTarget value).toReal)
    (value : α) :
    factor * (mix weight.val weight.property.1 weight.property.2 firstSource secondSource
      value).toReal ≤
      (mix weight.val weight.property.1 weight.property.2 firstTarget secondTarget
        value).toReal := by
  rw [mix_apply_toReal, mix_apply_toReal]
  have left := mul_le_mul_of_nonneg_left (first value) weight.property.1
  have right := mul_le_mul_of_nonneg_left (second value)
    (sub_nonneg.mpr weight.property.2)
  nlinarith

end GameTheory.Math.Probability
