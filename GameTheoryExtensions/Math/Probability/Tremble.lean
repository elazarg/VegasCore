/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Uniform action floors and independent local trembles

An epsilon tremble reserves epsilon probability for every action. Removing that
floor produces the residual law whose trembling realization is the original law.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Reserve epsilon mass for each action and use the supplied law for the rest. -/
def tremble (law : FinDist α) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon * Fintype.card α ≤ 1) : FinDist α :=
  mix (epsilon * Fintype.card α) (mul_nonneg nonnegative (Nat.cast_nonneg _)) small
    uniformOfFintype law

theorem prob_tremble (law : FinDist α) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon * Fintype.card α ≤ 1) (action : α) :
    (law.tremble epsilon nonnegative small).prob action =
      epsilon + (1 - epsilon * Fintype.card α) * law.prob action := by
  rw [tremble, prob_mix, prob_uniformOfFintype]
  have positive : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [mul_assoc, mul_inv_cancel₀ positive, mul_one]

theorem le_prob_tremble (law : FinDist α) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon * Fintype.card α ≤ 1) (action : α) :
    epsilon ≤ (law.tremble epsilon nonnegative small).prob action := by
  rw [prob_tremble]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr small) (law.prob_nonneg action))

/-- The residual randomization after removing a strictly smaller uniform floor. -/
def removeTremble (law : FinDist α) (epsilon : ℝ)
    (small : epsilon * Fintype.card α < 1) (floor : ∀ action, epsilon ≤ law.prob action) :
    FinDist α :=
  ofWeights (fun action => (law.prob action - epsilon) / (1 - epsilon * Fintype.card α))
    (fun action => div_nonneg (sub_nonneg.mpr (floor action)) (sub_pos.mpr small).le) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, sum_prob]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_comm (Fintype.card α : ℝ) epsilon,
        mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr small))])

omit [Nonempty α] in
theorem prob_removeTremble (law : FinDist α) (epsilon : ℝ)
    (small : epsilon * Fintype.card α < 1) (floor : ∀ action, epsilon ≤ law.prob action)
    (action : α) :
    (law.removeTremble epsilon small floor).prob action =
      (law.prob action - epsilon) / (1 - epsilon * Fintype.card α) :=
  prob_ofWeights ..

theorem tremble_removeTremble (law : FinDist α) (epsilon : ℝ)
    (nonnegative : 0 ≤ epsilon) (small : epsilon * Fintype.card α < 1)
    (floor : ∀ action, epsilon ≤ law.prob action) :
    (law.removeTremble epsilon small floor).tremble epsilon nonnegative small.le = law := by
  apply ext_of_prob
  intro action
  rw [prob_tremble, prob_removeTremble,
    mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr small))]
  ring

/-- Sampling a prescription and then trembling it is trembling its law. -/
theorem bind_tremble_pure (law : FinDist α) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon * Fintype.card α ≤ 1) :
    law.bind (fun action => (pure action).tremble epsilon nonnegative small) =
      law.tremble epsilon nonnegative small := by
  classical
  apply ext_of_prob
  intro action
  simp only [prob_bind, prob_tremble, expect_add, expect_const, expect_smul]
  rw [← prob_bind, bind_pure]

section Product

variable {Index : Type*} [Fintype Index] {A B : Index → Type*}

/-- Independent coordinate kernels commute with independent input sampling. -/
theorem pi_bind (laws : (index : Index) → FinDist (A index))
    (kernel : (index : Index) → A index → FinDist (B index)) :
    (pi laws).bind (fun input => pi fun index => kernel index (input index)) =
      pi (fun index => (laws index).bind (kernel index)) := by
  classical
  apply ext_of_prob
  intro output
  rw [prob_bind, prob_pi]
  conv_rhs => simp only [prob_bind, expect_eq_sum_support]
  rw [expect_eq_sum_of_subset _ _ (Fintype.piFinset fun index => (laws index).supportFinset)
    (support_pi_subset laws), Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [prob_pi, prob_pi, ← Finset.prod_mul_distrib]

/-- Conditioning independent choices on coordinate restrictions does not
change a coordinate whose restriction is the whole carrier. -/
theorem map_condOn_pi_of_unrestricted (laws : (index : Index) → FinDist (A index))
    (restriction : (index : Index) → Set (A index)) (selected : Index)
    (unrestricted : restriction selected = Set.univ)
    (positive : ∃ values ∈ {values | ∀ index, values index ∈ restriction index},
      values ∈ (pi laws).support) :
    ((pi laws).condOn {values | ∀ index, values index ∈ restriction index} positive).map
        (fun values => values selected) = laws selected := by
  classical
  have coordinate (index : Index) : ∃ value ∈ restriction index,
      value ∈ (laws index).support := by
    obtain ⟨values, permitted, supported⟩ := positive
    exact ⟨values index, permitted index, mem_support_pi.mp supported index⟩
  rw [condOn_pi laws restriction coordinate positive, map_apply_pi]
  simp only [unrestricted, condOn_univ]

/-- A mixture integrates the unnormalized mass of each branch's event. -/
theorem probOf_bind {Latent : Type*} {Value : Type*} (law : FinDist Latent)
    (kernel : Latent → FinDist Value) (event : Set Value) :
    (law.bind kernel).probOf event = law.expect (fun latent => (kernel latent).probOf event) := by
  classical
  simp only [← expect_indicator_eq_probOf, expect_bind]

/-- Correlating the prescribed coordinate laws does not lower a common action
floor after conditioning on restrictions of other coordinates. -/
theorem le_prob_condOn_mixture_pi {Latent : Type*} (law : FinDist Latent)
    (kernel : Latent → (index : Index) → FinDist (A index))
    (restriction : (index : Index) → Set (A index)) (selected : Index)
    (unrestricted : restriction selected = Set.univ) (action : A selected) (floor : ℝ)
    (bounded : ∀ latent ∈ law.support, floor ≤ (kernel latent selected).prob action)
    (positive : ∃ values ∈ {values | ∀ index, values index ∈ restriction index},
      values ∈ (law.bind fun latent => pi (kernel latent)).support) :
    floor ≤ (((law.bind fun latent => pi (kernel latent)).condOn
      {values | ∀ index, values index ∈ restriction index} positive).map
        (fun values => values selected)).prob action := by
  classical
  let event : Set ((index : Index) → A index) :=
    {values | ∀ index, values index ∈ restriction index}
  let answer : Set ((index : Index) → A index) :=
    (fun values => values selected) ⁻¹' {action}
  have branch (latent : Latent) (supported : latent ∈ law.support) :
      floor * (pi (kernel latent)).probOf event ≤
        (pi (kernel latent)).probOf (event ∩ answer) := by
    by_cases reached : ∃ values ∈ event, values ∈ (pi (kernel latent)).support
    · have marginal := map_condOn_pi_of_unrestricted (kernel latent)
        restriction selected unrestricted reached
      have lower := bounded latent supported
      rw [← marginal, prob_map_eq_probOf_preimage_singleton, probOf_condOn_eq_inter] at lower
      exact (le_div_iff₀ (probOf_pos reached)).mp lower
    · have zero : (pi (kernel latent)).probOf event = 0 := by
        rw [← expect_indicator_eq_probOf]
        calc
          _ = (pi (kernel latent)).expect (fun _ => 0) := by
            apply expect_congr
            intro values present
            exact ite_eq_right (fun permitted => reached ⟨values, permitted, present⟩)
          _ = 0 := expect_const _ 0
      rw [zero, mul_zero]
      exact ENNReal.toReal_nonneg
  rw [prob_map_eq_probOf_preimage_singleton, probOf_condOn_eq_inter]
  apply (le_div_iff₀ (probOf_pos positive)).mpr
  change floor * (law.bind fun latent => pi (kernel latent)).probOf event ≤
    (law.bind fun latent => pi (kernel latent)).probOf (event ∩ answer)
  rw [probOf_bind, probOf_bind, ← expect_smul]
  exact expect_mono branch

end Product

end GameTheory.Math.Probability.FinDist
