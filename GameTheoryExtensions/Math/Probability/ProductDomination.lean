/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Lower probability bounds under independent local perturbations

Replacing each coordinate law by an epsilon mixture with an arbitrary reference
retains at least `(1 - epsilon)^card` of every original joint probability.
The same lower bound survives any common subsequent kernel. These are
unconditional law comparisons; transporting conditional beliefs additionally
requires bounds relative to the probability of the conditioning event.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {Index : Type*} [Fintype Index] {Action : Index → Type*}

/-- Coordinate lower bounds multiply under independent sampling. -/
theorem prob_pi_ge_prod_mul (source target : ∀ index, FinDist (Action index))
    (factor : Index → ℝ) (nonnegative : ∀ index, 0 ≤ factor index)
    (dominates : ∀ index action,
      factor index * (source index).prob action ≤ (target index).prob action)
    (actions : ∀ index, Action index) :
    (∏ index, factor index) * (pi source).prob actions ≤ (pi target).prob actions := by
  simp only [prob_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro index _
    exact mul_nonneg (nonnegative index) ((source index).prob_nonneg _)
  · intro index _
    exact dominates index (actions index)

/-- Every original joint action retains the probability of choosing the
original branch independently at all coordinates. -/
theorem prob_pi_mix_lower (source reference : ∀ index, FinDist (Action index))
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (actions : ∀ index, Action index) :
    (1 - epsilon) ^ Fintype.card Index * (pi source).prob actions ≤
      (pi (fun index => mix epsilon nonnegative small (reference index) (source index))).prob
        actions := by
  have bound := prob_pi_ge_prod_mul source
    (fun index => mix epsilon nonnegative small (reference index) (source index))
    (fun _ => 1 - epsilon) (fun _ => sub_nonneg.mpr small) (fun index action => by
      rw [prob_mix]
      exact le_add_of_nonneg_left
        (mul_nonneg nonnegative ((reference index).prob_nonneg action))) actions
  simpa only [Finset.prod_const, Finset.card_univ] using bound

section Kernel

variable {State Next : Type*}

/-- A common kernel preserves pointwise domination, including on infinite
carriers with finitely supported input laws. -/
theorem prob_bind_ge_mul (source target : FinDist State) (factor : ℝ)
    (dominates : ∀ state, factor * source.prob state ≤ target.prob state)
    (kernel : State → FinDist Next) (next : Next) :
    factor * (source.bind kernel).prob next ≤ (target.bind kernel).prob next := by
  classical
  let support := source.supportFinset ∪ target.supportFinset
  have sourceSupport : source.support ⊆ support := by
    intro state member
    exact Finset.mem_union_left _ (source.mem_supportFinset.mpr member)
  have targetSupport : target.support ⊆ support := by
    intro state member
    exact Finset.mem_union_right _ (target.mem_supportFinset.mpr member)
  rw [prob_bind, prob_bind,
    expect_eq_sum_of_subset source _ support sourceSupport,
    expect_eq_sum_of_subset target _ support targetSupport, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro state _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (dominates state) ((kernel state).prob_nonneg next)

end Kernel

/-- The product bound applies after the actual common transition kernel. -/
theorem prob_pi_mix_bind_lower {Next : Type*}
    (source reference : ∀ index, FinDist (Action index))
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (kernel : (∀ index, Action index) → FinDist Next) (next : Next) :
    (1 - epsilon) ^ Fintype.card Index * ((pi source).bind kernel).prob next ≤
      ((pi (fun index => mix epsilon nonnegative small (reference index) (source index))).bind
        kernel).prob next :=
  prob_bind_ge_mul _ _ _ (prob_pi_mix_lower source reference epsilon nonnegative small) kernel next

end GameTheory.Math.Probability.FinDist
