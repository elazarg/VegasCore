/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.ExpectationContraction
import Mathlib.Probability.Distributions.Geometric

/-! # Why real kernel pullback retains integration guards

Unrestricted real functions do not give monotone expectation maps on infinite
carriers: a divergent weighted sum has totalized value zero. A signed transport
bridge must retain integration guards or restrict its observable fibers.
-/

noncomputable section

namespace GameTheoryExtensionsTests.SignedKernelPullback

open GameTheory.Math.Probability

/-- Every fully supported law on the naturals has an unbounded observable
above the constant one whose weighted sum diverges. -/
theorem unrestricted_expect_not_monotone (law : PMF ℕ)
    (supported : ∀ number, law number ≠ 0) :
    ¬ Monotone (fun observable : ℕ → ℝ => expect law observable) := by
  let divergent := fun number => ((law number).toReal)⁻¹
  have positive : ∀ number, 0 < (law number).toReal := fun number =>
    ENNReal.toReal_pos (supported number) (law.apply_ne_top number)
  have weighted : ∀ number, (law number).toReal * divergent number = 1 :=
    fun number => mul_inv_cancel₀ (positive number).ne'
  have notIntegrable : ¬ PayoffIntegrable law divergent := by
    rw [payoffIntegrable_iff_summable]
    simp only [weighted]
    simpa only [summable_const_iff] using (one_ne_zero : (1 : ℝ) ≠ 0)
  intro monotone
  have compared := monotone (show (fun _ : ℕ => (1 : ℝ)) ≤ divergent from fun number => by
    apply (one_le_inv₀ (positive number)).mpr
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal (law.apply_ne_top number) ENNReal.one_ne_top).mpr
        (law.coe_le_one number))
  change expect law (fun _ => (1 : ℝ)) ≤ expect law divergent at compared
  rw [expect_constant, expect_of_not_payoffIntegrable notIntegrable] at compared
  norm_num at compared

private def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

private def law : PMF ℕ := (ProbabilityTheory.geometricMeasure half).toPMF

theorem geometric_expect_not_monotone :
    ¬ Monotone (fun observable : ℕ → ℝ => expect law observable) := by
  apply unrestricted_expect_not_monotone
  intro number
  change ProbabilityTheory.geometricMeasure half {number} ≠ 0
  have nonzero : half ≠ 0 := by
    intro same
    have := congrArg (fun value : unitInterval => (value : ℝ)) same
    norm_num [half] at this
  rw [ProbabilityTheory.geometricMeasure_singleton nonzero]
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  change (0 : ℝ) < (1 - (1 / 2 : ℝ)) ^ number * (1 / 2)
  positivity

end GameTheoryExtensionsTests.SignedKernelPullback
