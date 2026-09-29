/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Mixture
import Mathlib.Probability.Distributions.Uniform
import GameTheory.Math.Probability.Expectation

/-! # Uniform laws on finite sets -/

noncomputable section

open scoped ENNReal

namespace GameTheory.Math.Probability

variable {α : Type*}

/-- Every point of a finite nonempty carrier has real mass one over its size. -/
theorem toReal_uniformOfFintype_apply [Fintype α] [Nonempty α] (a : α) :
    ((PMF.uniformOfFintype α) a).toReal = (Fintype.card α : ℝ)⁻¹ := by
  rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The uniform expectation is the average over the carrier. -/
theorem expect_uniformOfFintype [Fintype α] [Nonempty α] (value : α → ℝ) :
    expect (PMF.uniformOfFintype α) value = (∑ a, value a) / Fintype.card α := by
  rw [expect_eq_sum]
  simp_rw [toReal_uniformOfFintype_apply]
  rw [← Finset.mul_sum, div_eq_inv_mul]

/-- Adding one distinct candidate scales every old candidate equally. -/
theorem uniformOfFinset_insert [DecidableEq α] (members : Finset α)
    (nonempty : members.Nonempty) (fresh : α) (absent : fresh ∉ members) :
    PMF.uniformOfFinset (insert fresh members) (Finset.insert_nonempty fresh members) =
      mix ((members.card : ℝ) + 1)⁻¹
        (inv_nonneg.mpr (by positivity))
        (by rw [inv_le_one₀ (by positivity)]; have := Nat.cast_nonneg (α := ℝ) members.card;
            linarith)
        (PMF.pure fresh) (PMF.uniformOfFinset members nonempty) := by
  have positive : (0 : ℝ) < members.card := by exact_mod_cast nonempty.card_pos
  have cardReal : ((members.card : ℝ≥0∞) + 1).toReal = members.card + 1 := by
    exact_mod_cast ENNReal.toReal_natCast (members.card + 1)
  ext value
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    mix_apply_toReal]
  by_cases same : value = fresh
  · subst value
    simp [PMF.uniformOfFinset_apply, absent, Finset.card_insert_of_notMem absent, cardReal]
  · by_cases member : value ∈ members
    · simp only [PMF.uniformOfFinset_apply, Finset.mem_insert, same, member, or_true,
        ↓reduceIte, Finset.card_insert_of_notMem absent, PMF.pure_apply, ENNReal.toReal_inv,
        Nat.cast_add, Nat.cast_one, cardReal, ENNReal.toReal_natCast, ENNReal.toReal_zero,
        mul_zero, zero_add]
      field_simp
      ring
    · simp [PMF.uniformOfFinset_apply, same, member, PMF.pure_apply]

end GameTheory.Math.Probability
