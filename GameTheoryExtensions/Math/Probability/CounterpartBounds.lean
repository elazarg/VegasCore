/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Mass bounds from counterparts with bounded fibers

Several bad points may use the same good counterpart. The relevant constant
is the largest number of bad points in one counterpart fiber. Normalizing the
weights sharpens a relative bound `bad ≤ c * good` to `bad / total ≤ c / (1 + c)`.
-/

namespace GameTheory.Math.Probability

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] (weight : α → ℝ)
  (bad : α → Prop) [DecidablePred bad] (counterpart : α → α)
  (multiplicity : ℕ) {ratio : ℝ}

/-- A pointwise domination estimate sums with the actual bad-fiber multiplicity,
rather than the cardinality of the entire carrier. -/
theorem sum_weights_le_of_bounded_counterpart (nonneg : ∀ point, 0 ≤ weight point)
    (ratioNonneg : 0 ≤ ratio)
    (good : ∀ point, bad point → ¬ bad (counterpart point))
    (fibers : ∀ point, ¬ bad point →
      ((univ.filter bad).filter fun original => counterpart original = point).card ≤ multiplicity)
    (dominated : ∀ point, bad point → weight point ≤ ratio * weight (counterpart point)) :
    ∑ point with bad point, weight point ≤
      (multiplicity * ratio) * ∑ point with ¬ bad point, weight point := by
  classical
  have regroup : ∑ point with bad point, weight (counterpart point) =
      ∑ point with ¬ bad point,
        ((univ.filter bad).filter fun original => counterpart original = point).card *
          weight point := by
    rw [← sum_fiberwise_of_maps_to (g := counterpart) (t := univ.filter fun point => ¬ bad point)
      fun point member => mem_filter.mpr ⟨mem_univ _, good point (mem_filter.mp member).2⟩]
    refine sum_congr rfl fun point _ => ?_
    rw [sum_congr rfl fun original member => by rw [(mem_filter.mp member).2], sum_const,
      nsmul_eq_mul]
  calc
    ∑ point with bad point, weight point
        ≤ ∑ point with bad point, ratio * weight (counterpart point) :=
      sum_le_sum fun point member => dominated point (mem_filter.mp member).2
    _ = ratio * ∑ point with ¬ bad point,
        ((univ.filter bad).filter fun original => counterpart original = point).card *
          weight point := by rw [← mul_sum, regroup]
    _ ≤ ratio * ∑ point with ¬ bad point, (multiplicity : ℝ) * weight point := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun point member => ?_) ratioNonneg
      refine mul_le_mul_of_nonneg_right ?_ (nonneg point)
      exact_mod_cast fibers point (mem_filter.mp member).2
    _ = (multiplicity * ratio) * ∑ point with ¬ bad point, weight point := by
      rw [← mul_sum]
      ring

/-- The normalized counterpart bound. Positive total mass is necessary for the
normalization; no positive mass is required of an individual point. -/
theorem sum_weights_div_sum_le_of_bounded_counterpart
    (nonneg : ∀ point, 0 ≤ weight point) (positive : 0 < ∑ point, weight point)
    (ratioNonneg : 0 ≤ ratio)
    (good : ∀ point, bad point → ¬ bad (counterpart point))
    (fibers : ∀ point, ¬ bad point →
      ((univ.filter bad).filter fun original => counterpart original = point).card ≤ multiplicity)
    (dominated : ∀ point, bad point → weight point ≤ ratio * weight (counterpart point)) :
    (∑ point with bad point, weight point) / (∑ point, weight point) ≤
      (multiplicity * ratio) / (1 + multiplicity * ratio) := by
  have bound := sum_weights_le_of_bounded_counterpart weight bad counterpart multiplicity
    nonneg ratioNonneg good fibers dominated
  have scaleNonneg : 0 ≤ (multiplicity : ℝ) * ratio :=
    mul_nonneg (Nat.cast_nonneg _) ratioNonneg
  rw [div_le_div_iff₀ positive (by positivity)]
  rw [← sum_filter_add_sum_filter_not univ bad weight]
  nlinarith

end GameTheory.Math.Probability
