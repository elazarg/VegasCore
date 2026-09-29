/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Support
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Lower probability bounds under independent local perturbations

Replacing each coordinate law by an epsilon mixture with an arbitrary reference
retains at least `(1 - epsilon)^card` of every original joint probability.
The same lower bound survives any common subsequent kernel. These are
unconditional law comparisons; transporting conditional beliefs additionally
requires bounds relative to the probability of the conditioning event.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {Index : Type*} [Fintype Index] {Action : Index → Type*}

/-- Coordinate lower bounds multiply under independent sampling. -/
theorem prob_pi_ge_prod_mul (source target : ∀ index, PMF (Action index))
    (factor : Index → ℝ) (nonnegative : ∀ index, 0 ≤ factor index)
    (dominates : ∀ index action,
      factor index * ((source index) action).toReal ≤ ((target index) action).toReal)
    (actions : ∀ index, Action index) :
    (∏ index,
        factor index) * ((independentProduct source) actions).toReal ≤ ((independentProduct target)
            actions).toReal := by
  simp only [independentProduct_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro index _
    exact mul_nonneg (nonnegative index) ENNReal.toReal_nonneg
  · intro index _
    exact dominates index (actions index)

/-- Every original joint action retains the probability of choosing the
original branch independently at all coordinates. -/
theorem prob_pi_mix_lower (source reference : ∀ index, PMF (Action index))
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (actions : ∀ index, Action index) :
    (1 - epsilon) ^ Fintype.card Index * ((independentProduct source) actions).toReal ≤
      ((independentProduct fun index =>
        mix epsilon nonnegative small (reference index) (source index)) actions).toReal := by
  have bound := prob_pi_ge_prod_mul source
    (fun index => mix epsilon nonnegative small (reference index) (source index))
    (fun _ => 1 - epsilon) (fun _ => sub_nonneg.mpr small) (fun index action => by
      rw [mix_apply_toReal]
      exact le_add_of_nonneg_left (mul_nonneg nonnegative ENNReal.toReal_nonneg)) actions
  simpa only [Finset.prod_const, Finset.card_univ] using bound

section Kernel

variable {State Next : Type*}

/-- A common kernel preserves pointwise domination. -/
theorem prob_bind_ge_mul (source target : PMF State) (factor : ℝ)
    (dominates : ∀ state, factor * (source state).toReal ≤ (target state).toReal)
    (kernel : State → PMF Next) (next : Next) :
    factor * ((source.bind kernel) next).toReal ≤ ((target.bind kernel) next).toReal := by
  rw [toReal_bind_apply, toReal_bind_apply, expect, expect, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun state => ?_)
    ((payoffIntegrable_toReal_apply source kernel next).summable.mul_left factor)
    (payoffIntegrable_toReal_apply target kernel next).summable
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (dominates state) ENNReal.toReal_nonneg

end Kernel

/-- The product bound applies after the actual common transition kernel. -/
theorem prob_pi_mix_bind_lower {Next : Type*}
    (source reference : ∀ index, PMF (Action index))
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (kernel : (∀ index, Action index) → PMF Next) (next : Next) :
    (1 - epsilon) ^ Fintype.card Index * (((independentProduct source).bind kernel) next).toReal ≤
      (((independentProduct (fun index => mix epsilon nonnegative small (reference index) (source
          index))).bind
        kernel) next).toReal :=
  prob_bind_ge_mul _ _ _ (prob_pi_mix_lower source reference epsilon nonnegative small) kernel next

end PMF
