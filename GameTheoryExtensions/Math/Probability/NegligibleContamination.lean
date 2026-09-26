/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Convergence

/-! # Preserving conditional beliefs when contaminating histories vanish faster

The information event may itself have probability tending to zero. What matters
is the ratio of contaminating mass to the surviving compliant mass, not the
unconditional probability of a forbidden history alone.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

namespace FinDist

variable {α : Type*}

private theorem event_mass_nonnegative (law : FinDist α) (event : Set α) :
    0 ≤ law.probOf event := ENNReal.toReal_nonneg

private theorem point_mass_le_event (law : FinDist α) (event : Set α)
    (value : α) (member : value ∈ event) : law.prob value ≤ law.probOf event := by
  classical
  rw [← expect_indicator_eq_probOf]
  have point := expect_ite_eq law value 1
  rw [mul_one] at point
  rw [← point]
  apply expect_mono
  intro candidate _
  by_cases same : value = candidate
  · subst candidate
    simp only [ite_true, ite_eq_left member, le_refl]
  · simp only [ite_eq_right same]
    split_ifs <;> norm_num

private theorem event_mass_split (law : FinDist α) (whole good : Set α)
    (subset : good ⊆ whole) :
    law.probOf whole = law.probOf good + law.probOf (whole \ good) := by
  classical
  simp only [← expect_indicator_eq_probOf, ← expect_add]
  apply expect_congr
  intro value _
  by_cases inGood : value ∈ good
  · simp [inGood, subset inGood]
  · by_cases inWhole : value ∈ whole <;> simp [inGood, inWhole]

/-- Pointwise posterior error is bounded by the contaminating-to-compliant
mass ratio. No positive lower bound on the whole event's mass is required. -/
theorem conditional_contamination_bound (law : FinDist α) (whole good : Set α)
    (subset : good ⊆ whole)
    (wholeMeet : ∃ value ∈ whole, value ∈ law.support)
    (goodMeet : ∃ value ∈ good, value ∈ law.support) (value : α) :
    |(law.condOn whole wholeMeet).prob value - (law.condOn good goodMeet).prob value| ≤
      law.probOf (whole \ good) / law.probOf good := by
  classical
  have goodPositive := probOf_pos goodMeet
  have wholePositive := probOf_pos wholeMeet
  have badNonnegative := event_mass_nonnegative law (whole \ good)
  have splitMass := event_mass_split law whole good subset
  have massLe : law.probOf good ≤ law.probOf whole := by linarith
  rw [prob_condOn, prob_condOn]
  by_cases inGood : value ∈ good
  · rw [ite_eq_left inGood, ite_eq_left (subset inGood)]
    have pointLe := point_mass_le_event law whole value (subset inGood)
    have fractionLe : law.prob value / law.probOf whole ≤ 1 :=
      (div_le_one wholePositive).mpr pointLe
    have ordered : law.prob value / law.probOf whole ≤ law.prob value / law.probOf good :=
      div_le_div_of_nonneg_left (law.prob_nonneg value) goodPositive massLe
    rw [abs_of_nonpos (sub_nonpos.mpr ordered), neg_sub]
    apply (le_div_iff₀ goodPositive).mpr
    calc
      (law.prob value / law.probOf good - law.prob value / law.probOf whole) *
          law.probOf good = law.prob value -
            (law.prob value / law.probOf whole) * law.probOf good := by
        rw [sub_mul, div_mul_cancel₀ _ goodPositive.ne']
      _ = (law.prob value / law.probOf whole) * law.probOf (whole \ good) := by
        have cancellation := div_mul_cancel₀ (law.prob value) wholePositive.ne'
        calc
          _ = (law.prob value / law.probOf whole) *
              (law.probOf whole - law.probOf good) := by
            rw [mul_sub, cancellation]
          _ = _ := by congr 1; linarith
      _ ≤ law.probOf (whole \ good) := mul_le_of_le_one_left badNonnegative fractionLe
  · rw [ite_eq_right inGood]
    by_cases inWhole : value ∈ whole
    · rw [ite_eq_left inWhole, sub_zero,
        abs_of_nonneg (div_nonneg (law.prob_nonneg value) wholePositive.le)]
      have pointLe := point_mass_le_event law (whole \ good) value ⟨inWhole, inGood⟩
      exact (div_le_div_of_nonneg_right pointLe wholePositive.le).trans
        (div_le_div_of_nonneg_left badNonnegative goodPositive massLe)
    · rw [ite_eq_right inWhole, sub_zero, abs_zero]
      exact div_nonneg badNonnegative goodPositive.le

end FinDist

/-- The retained information set may be off path in the limit. Its Bayes
belief is still preserved when the contaminating mass is negligible relative
to the compliant part of that same set. -/
theorem conditional_contamination_converges {α : Type*}
    (sequence : ℕ → FinDist α) (whole good : Set α) (subset : good ⊆ whole)
    (wholeMeet : ∀ n, ∃ value ∈ whole, value ∈ (sequence n).support)
    (goodMeet : ∀ n, ∃ value ∈ good, value ∈ (sequence n).support)
    (limit : FinDist α)
    (compliant : FinDistConvergesPointwise
      (fun n => (sequence n).condOn good (goodMeet n)) limit)
    (negligible : Tendsto (fun n =>
      (sequence n).probOf (whole \ good) / (sequence n).probOf good) atTop (nhds 0)) :
    FinDistConvergesPointwise
      (fun n => (sequence n).condOn whole (wholeMeet n)) limit := by
  intro value
  apply (compliant value).congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ negligible
  intro n
  simpa only [Real.dist_eq, abs_sub_comm] using
    FinDist.conditional_contamination_bound (sequence n) whole good subset
      (wholeMeet n) (goodMeet n) value

/-- A lower bound on each compliant fiber mass and an upper bound on all
contaminating histories suffice. In a finite game the former can be the
minimum positive source-history probability along its consistency sequence. -/
theorem conditional_contamination_converges_of_bound {α : Type*}
    (sequence : ℕ → FinDist α) (whole good : Set α) (subset : good ⊆ whole)
    (wholeMeet : ∀ n, ∃ value ∈ whole, value ∈ (sequence n).support)
    (goodMeet : ∀ n, ∃ value ∈ good, value ∈ (sequence n).support)
    (limit : FinDist α)
    (compliant : FinDistConvergesPointwise
      (fun n => (sequence n).condOn good (goodMeet n)) limit)
    (lower upper : ℕ → ℝ) (positive : ∀ n, 0 < lower n)
    (goodBound : ∀ n, lower n ≤ (sequence n).probOf good)
    (badBound : ∀ n, (sequence n).probOf (whole \ good) ≤ upper n)
    (negligible : Tendsto (fun n => upper n / lower n) atTop (nhds 0)) :
    FinDistConvergesPointwise
      (fun n => (sequence n).condOn whole (wholeMeet n)) limit := by
  apply conditional_contamination_converges sequence whole good subset wholeMeet goodMeet limit
    compliant
  apply squeeze_zero _ _ negligible
  · intro n
    exact div_nonneg ENNReal.toReal_nonneg (FinDist.probOf_pos (goodMeet n)).le
  · intro n
    have nonnegative : 0 ≤ (sequence n).probOf (whole \ good) := ENNReal.toReal_nonneg
    exact (div_le_div_of_nonneg_right (badBound n)
      (FinDist.probOf_pos (goodMeet n)).le).trans
        (div_le_div_of_nonneg_left (nonnegative.trans (badBound n))
          (positive n) (goodBound n))

end GameTheory.Math.Probability
