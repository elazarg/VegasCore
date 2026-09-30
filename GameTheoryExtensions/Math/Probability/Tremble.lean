/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import Mathlib.Probability.Distributions.Uniform
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheory.Math.Probability.ProductConditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Uniform action floors and independent local trembles

An epsilon tremble reserves epsilon probability for every action. Removing that
floor produces the residual law whose trembling realization is the original law.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Reserve epsilon mass for each action and use the supplied law for the rest. -/
def tremble (law : PMF α) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon * Fintype.card α ≤ 1) : PMF α :=
  mix (epsilon * Fintype.card α) (mul_nonneg nonnegative (Nat.cast_nonneg _)) small
    (uniformOfFintype α) law

theorem prob_tremble (law : PMF α) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon * Fintype.card α ≤ 1) (action : α) :
    ((law.tremble epsilon nonnegative small) action).toReal =
      epsilon + (1 - epsilon * Fintype.card α) * (law action).toReal := by
  rw [tremble, mix_apply_toReal, uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  have positive : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [mul_assoc, mul_inv_cancel₀ positive, mul_one]

theorem le_prob_tremble (law : PMF α) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon * Fintype.card α ≤ 1) (action : α) :
    epsilon ≤ ((law.tremble epsilon nonnegative small) action).toReal := by
  rw [prob_tremble]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr small) ENNReal.toReal_nonneg)

/-- The residual randomization after removing a strictly smaller uniform floor. -/
def removeTremble (law : PMF α) (epsilon : ℝ)
    (small : epsilon * Fintype.card α < 1) (floor : ∀ action, epsilon ≤ (law action).toReal) :
    PMF α :=
  ofFintype
    (fun action => ENNReal.ofReal (((law action).toReal - epsilon) /
      (1 - epsilon * Fintype.card α))) (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun action _ =>
        div_nonneg (sub_nonneg.mpr (floor action)) (sub_pos.mpr small).le]
      simp only [div_eq_mul_inv]
      have total : ∑ action, (law action).toReal = 1 := by
        simpa [tsum_fintype] using pmf_weight_tsum_one law
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, total]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_comm (Fintype.card α : ℝ) epsilon,
        mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr small)), ENNReal.ofReal_one])

omit [Nonempty α] in
theorem prob_removeTremble (law : PMF α) (epsilon : ℝ)
    (small : epsilon * Fintype.card α < 1) (floor : ∀ action, epsilon ≤ (law action).toReal)
    (action : α) :
    ((law.removeTremble epsilon small floor) action).toReal =
      ((law action).toReal - epsilon) / (1 - epsilon * Fintype.card α) := by
  rw [removeTremble, ofFintype_apply, ENNReal.toReal_ofReal
    (div_nonneg (sub_nonneg.mpr (floor action)) (sub_pos.mpr small).le)]

theorem tremble_removeTremble (law : PMF α) (epsilon : ℝ)
    (nonnegative : 0 ≤ epsilon) (small : epsilon * Fintype.card α < 1)
    (floor : ∀ action, epsilon ≤ (law action).toReal) :
    (law.removeTremble epsilon small floor).tremble epsilon nonnegative small.le = law := by
  apply pmf_ext_toReal
  intro action
  rw [prob_tremble, prob_removeTremble,
    mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr small))]
  ring

/-- Sampling a prescription and then trembling it is trembling its law. -/
theorem bind_tremble_pure (law : PMF α) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon * Fintype.card α ≤ 1) :
    law.bind (fun action => (PMF.pure action).tremble epsilon nonnegative small) =
      law.tremble epsilon nonnegative small := by
  classical
  apply pmf_ext_toReal
  intro action
  rw [toReal_bind_apply, prob_tremble]
  simp only [prob_tremble]
  rw [expect_add (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_bounded _ _ (C := |1 - epsilon * Fintype.card α|) fun choice => by
        rw [abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg (a := (PMF.pure choice) action))]
        exact mul_le_of_le_one_right (abs_nonneg _) (pmf_toReal_apply_le_one _ _)),
    expect_constant, expect_const_mul, ← toReal_bind_apply, PMF.bind_pure]

end PMF
