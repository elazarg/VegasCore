/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Mixture
import Mathlib.Probability.Distributions.Uniform
import GameTheory.Math.Probability.Expectation
import GameTheory.Math.Probability.Uniform

/-! # Uniform laws on finite sets -/

noncomputable section

open scoped ENNReal

namespace GameTheory.Math.Probability

variable {α : Type*}

/-- Every point of a finite nonempty carrier has real mass one over its size. -/
theorem toReal_uniformOfFintype_apply [Fintype α] [Nonempty α] (a : α) :
    ((PMF.uniformOfFintype α) a).toReal = (Fintype.card α : ℝ)⁻¹ := by
  rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- A mixture is supported inside the union of its components' supports. -/
theorem support_mix_subset (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : PMF α) :
    (mix t h0 h1 μ ν).support ⊆ μ.support ∪ ν.support := by
  intro value member
  by_contra neither
  simp only [Set.mem_union, PMF.mem_support_iff, not_or, not_not] at neither
  rw [PMF.mem_support_iff, mix_apply] at member
  simp [neither.1, neither.2] at member

end GameTheory.Math.Probability
