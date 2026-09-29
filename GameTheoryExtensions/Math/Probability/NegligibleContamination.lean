/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Convergence
import GameTheoryExtensions.Math.Probability.Conditioning

/-! # Preserving conditional beliefs when contaminating histories vanish faster

The information event may itself have probability tending to zero. What matters
is the ratio of contaminating mass to the surviving compliant mass, not the
unconditional probability of a forbidden history alone.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

variable {α : Type*}

private theorem event_mass_nonnegative (law : PMF α) (event : Set α) :
    0 ≤ (law.toOuterMeasure event).toReal := ENNReal.toReal_nonneg

private theorem point_mass_le_event (law : PMF α) (event : Set α)
    (value : α) (member : value ∈ event) :
    (law value).toReal ≤ (law.toOuterMeasure event).toReal := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  exact ENNReal.toReal_mono (outerMeasure_ne_top law event)
    (law.toOuterMeasure.mono (Set.singleton_subset_iff.mpr member))

private theorem event_mass_split (law : PMF α) (whole good : Set α)
    (subset : good ⊆ whole) :
    (law.toOuterMeasure whole).toReal =
      (law.toOuterMeasure good).toReal + (law.toOuterMeasure (whole \ good)).toReal := by
  rw [← ENNReal.toReal_add (outerMeasure_ne_top law good) (outerMeasure_ne_top law _),
    PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_add]
  congr 1
  apply tsum_congr
  intro value
  by_cases inGood : value ∈ good
  · simp [Set.indicator, inGood, subset inGood]
  · by_cases inWhole : value ∈ whole <;> simp [Set.indicator, inGood, inWhole]

/-- Pointwise posterior error is bounded by the contaminating-to-compliant
mass ratio. No positive lower bound on the whole event's mass is required. -/
theorem conditional_contamination_bound (law : PMF α) (whole good : Set α)
    (subset : good ⊆ whole)
    (wholeMeet : ∃ value ∈ whole, value ∈ law.support)
    (goodMeet : ∃ value ∈ good, value ∈ law.support) (value : α) :
    |((law.filter whole wholeMeet) value).toReal - ((law.filter good goodMeet) value).toReal| ≤
      (law.toOuterMeasure (whole \ good)).toReal / (law.toOuterMeasure good).toReal := by
  classical
  have goodPositive := toOuterMeasure_toReal_pos law goodMeet
  have wholePositive := toOuterMeasure_toReal_pos law wholeMeet
  have badNonnegative := event_mass_nonnegative law (whole \ good)
  have splitMass := event_mass_split law whole good subset
  have massLe : (law.toOuterMeasure good).toReal ≤ (law.toOuterMeasure whole).toReal := by linarith
  rw [toReal_filter_apply, toReal_filter_apply]
  by_cases inGood : value ∈ good
  · rw [ite_eq_left inGood, ite_eq_left (subset inGood)]
    have pointLe := point_mass_le_event law whole value (subset inGood)
    have fractionLe : (law value).toReal / (law.toOuterMeasure whole).toReal ≤ 1 :=
      (div_le_one wholePositive).mpr pointLe
    have ordered : (law value).toReal / (law.toOuterMeasure whole).toReal ≤ (law value).toReal /
        (law.toOuterMeasure good).toReal :=
      div_le_div_of_nonneg_left ENNReal.toReal_nonneg goodPositive massLe
    rw [abs_of_nonpos (sub_nonpos.mpr ordered), neg_sub]
    apply (le_div_iff₀ goodPositive).mpr
    calc
      ((law value).toReal / (law.toOuterMeasure good).toReal - (law value).toReal /
          (law.toOuterMeasure whole).toReal) *
          (law.toOuterMeasure good).toReal = (law value).toReal -
            ((law value).toReal / (law.toOuterMeasure whole).toReal) * (law.toOuterMeasure
                good).toReal := by
        rw [sub_mul, div_mul_cancel₀ _ goodPositive.ne']
      _ = ((law value).toReal / (law.toOuterMeasure whole).toReal) * (law.toOuterMeasure (whole \
          good)).toReal := by
        have cancellation := div_mul_cancel₀ ((law value).toReal) wholePositive.ne'
        calc
          _ = ((law value).toReal / (law.toOuterMeasure whole).toReal) *
              ((law.toOuterMeasure whole).toReal - (law.toOuterMeasure good).toReal) := by
            rw [mul_sub, cancellation]
          _ = _ := by congr 1; linarith
      _ ≤ (law.toOuterMeasure (whole \ good)).toReal := mul_le_of_le_one_left badNonnegative
          fractionLe
  · rw [ite_eq_right inGood]
    by_cases inWhole : value ∈ whole
    · rw [ite_eq_left inWhole, sub_zero,
        abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg wholePositive.le)]
      have pointLe := point_mass_le_event law (whole \ good) value ⟨inWhole, inGood⟩
      exact (div_le_div_of_nonneg_right pointLe wholePositive.le).trans
        (div_le_div_of_nonneg_left badNonnegative goodPositive massLe)
    · rw [ite_eq_right inWhole, sub_zero, abs_zero]
      exact div_nonneg badNonnegative goodPositive.le

/-- The retained information set may be off path in the limit. Its Bayes
belief is still preserved when the contaminating mass is negligible relative
to the compliant part of that same set. -/
theorem conditional_contamination_converges {α : Type*}
    (sequence : ℕ → PMF α) (whole good : Set α) (subset : good ⊆ whole)
    (wholeMeet : ∀ n, ∃ value ∈ whole, value ∈ (sequence n).support)
    (goodMeet : ∀ n, ∃ value ∈ good, value ∈ (sequence n).support)
    (limit : PMF α)
    (compliant : PMFConvergesPointwise
      (fun n => (sequence n).filter good (goodMeet n)) limit)
    (negligible : Tendsto (fun n =>
      ((sequence n).toOuterMeasure (whole \ good)).toReal / ((sequence n).toOuterMeasure
          good).toReal) atTop (nhds 0)) :
    PMFConvergesPointwise
      (fun n => (sequence n).filter whole (wholeMeet n)) limit := by
  rw [pmfConvergesPointwise_iff_toReal]
  intro value
  apply (compliant.toReal value).congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ negligible
  intro n
  simpa only [Real.dist_eq, abs_sub_comm] using
    conditional_contamination_bound (sequence n) whole good subset
      (wholeMeet n) (goodMeet n) value

/-- A lower bound on each compliant fiber mass and an upper bound on all
contaminating histories suffice. In a finite game the former can be the
minimum positive source-history probability along its consistency sequence. -/
theorem conditional_contamination_converges_of_bound {α : Type*}
    (sequence : ℕ → PMF α) (whole good : Set α) (subset : good ⊆ whole)
    (wholeMeet : ∀ n, ∃ value ∈ whole, value ∈ (sequence n).support)
    (goodMeet : ∀ n, ∃ value ∈ good, value ∈ (sequence n).support)
    (limit : PMF α)
    (compliant : PMFConvergesPointwise
      (fun n => (sequence n).filter good (goodMeet n)) limit)
    (lower upper : ℕ → ℝ) (positive : ∀ n, 0 < lower n)
    (goodBound : ∀ n, lower n ≤ ((sequence n).toOuterMeasure good).toReal)
    (badBound : ∀ n, ((sequence n).toOuterMeasure (whole \ good)).toReal ≤ upper n)
    (negligible : Tendsto (fun n => upper n / lower n) atTop (nhds 0)) :
    PMFConvergesPointwise
      (fun n => (sequence n).filter whole (wholeMeet n)) limit := by
  apply conditional_contamination_converges sequence whole good subset wholeMeet goodMeet limit
    compliant
  apply squeeze_zero _ _ negligible
  · intro n
    exact div_nonneg ENNReal.toReal_nonneg (toOuterMeasure_toReal_pos _ (goodMeet n)).le
  · intro n
    have nonnegative : 0 ≤ ((sequence n).toOuterMeasure (whole \ good)).toReal :=
        ENNReal.toReal_nonneg
    exact (div_le_div_of_nonneg_right (badBound n)
      (toOuterMeasure_toReal_pos _ (goodMeet n)).le).trans
        (div_le_div_of_nonneg_left (nonnegative.trans (badBound n))
          (positive n) (goodBound n))

end GameTheory.Math.Probability
