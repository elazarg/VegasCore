/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import Mathlib.Probability.Distributions.Uniform
import GameTheoryExtensions.Math.Probability.Uniform

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

section Product

variable {Index : Type*} [Fintype Index] {A : Index → Type*}

/-- Conditioning independent choices on coordinate restrictions does not
change a coordinate whose restriction is the whole carrier. -/
theorem map_filter_independentProduct_of_unrestricted (laws : (index : Index) → PMF (A index))
    (restriction : (index : Index) → Set (A index)) (selected : Index)
    (unrestricted : restriction selected = Set.univ)
    (positive : ∃ values ∈ {values | ∀ index, values index ∈ restriction index},
      values ∈ (independentProduct laws).support) :
    ((independentProduct laws).filter {values | ∀ index, values index ∈ restriction index}
        positive).map (fun values => values selected) = laws selected := by
  classical
  have coordinate (index : Index) : ∃ value ∈ restriction index,
      value ∈ (laws index).support := by
    obtain ⟨values, permitted, supported⟩ := positive
    exact ⟨values index, permitted index,
      (independentProduct_support_iff laws values).mp supported index⟩
  have event : {values : (index : Index) → A index | ∀ index, values index ∈ restriction index} =
      Set.pi Set.univ restriction := by
    ext values
    simp
  have product := filter_independentProduct laws restriction coordinate
  simp only [← event] at product
  rw [product, independentProduct_map_eval]
  apply filter_of_support_subset
  rw [unrestricted]
  exact Set.subset_univ _

/-- Correlating the prescribed coordinate laws does not lower a common action
floor after conditioning on restrictions of other coordinates. -/
theorem le_prob_filter_mixture_independentProduct {Latent : Type*} (law : PMF Latent)
    (kernel : Latent → (index : Index) → PMF (A index))
    (restriction : (index : Index) → Set (A index)) (selected : Index)
    (unrestricted : restriction selected = Set.univ) (action : A selected) (floor : ℝ)
    (bounded : ∀ latent ∈ law.support, floor ≤ ((kernel latent selected) action).toReal)
    (positive : ∃ values ∈ {values | ∀ index, values index ∈ restriction index},
      values ∈ (law.bind fun latent => independentProduct (kernel latent)).support) :
    floor ≤ ((((law.bind fun latent => independentProduct (kernel latent)).filter
      {values | ∀ index, values index ∈ restriction index} positive).map
        (fun values => values selected)) action).toReal := by
  classical
  let event : Set ((index : Index) → A index) :=
    {values | ∀ index, values index ∈ restriction index}
  let answer : Set ((index : Index) → A index) :=
    (fun values => values selected) ⁻¹' {action}
  have filtered (law : PMF ((index : Index) → A index))
      (meets : ∃ values ∈ event, values ∈ law.support) :
      (((law.filter event meets).map fun values => values selected) action).toReal *
          (law.toOuterMeasure event).toReal =
        (law.toOuterMeasure (event ∩ answer)).toReal := by
    rw [← ENNReal.toReal_mul, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      toOuterMeasure_filter_apply, Set.inter_comm, ENNReal.div_mul_cancel
        ((toOuterMeasure_ne_zero_iff _ _).mpr meets) (outerMeasure_ne_top _ _)]
  have positiveMass (law : PMF ((index : Index) → A index))
      (meets : ∃ values ∈ event, values ∈ law.support) :
      0 < (law.toOuterMeasure event).toReal := by
    exact ENNReal.toReal_pos ((toOuterMeasure_ne_zero_iff _ _).mpr meets)
      (outerMeasure_ne_top _ _)
  have branch (latent : Latent) (supported : latent ∈ law.support) :
      floor * ((independentProduct (kernel latent)).toOuterMeasure event).toReal ≤
        ((independentProduct (kernel latent)).toOuterMeasure (event ∩ answer)).toReal := by
    by_cases reached : ∃ values ∈ event, values ∈ (independentProduct (kernel latent)).support
    · have marginal := map_filter_independentProduct_of_unrestricted (kernel latent)
        restriction selected unrestricted reached
      have lower := bounded latent supported
      rw [← marginal] at lower
      rw [← filtered _ reached]
      exact mul_le_mul_of_nonneg_right lower ENNReal.toReal_nonneg
    · have zero : (independentProduct (kernel latent)).toOuterMeasure event = 0 := by
        rw [PMF.toOuterMeasure_apply_eq_zero_iff]
        exact Set.disjoint_left.mpr fun values supported member =>
          reached ⟨values, member, supported⟩
      rw [zero, ENNReal.toReal_zero, mul_zero]
      exact ENNReal.toReal_nonneg
  have combined := filtered _ positive
  apply le_of_mul_le_mul_right _ (positiveMass _ positive)
  rw [combined, toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind, ← expect_const_mul]
  have bounds (target : Set ((index : Index) → A index)) :
      PayoffIntegrable law fun latent =>
        ((independentProduct (kernel latent)).toOuterMeasure target).toReal :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun latent => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using outerMeasure_le_one _ _)
  exact expect_mono branch
    (payoffIntegrable_of_bounded _ _ (C := |floor|) fun latent => by
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using outerMeasure_le_one _ _))
    (bounds _)

end Product

end PMF
