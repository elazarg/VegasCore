/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.ProductDecorrelation
import GameTheoryExtensions.Math.Probability.ProductTransport

/-! # Decorrelation near uncorrelated weights

A law on a finite type that is within `d` in `ℓ¹` of the normalization of
nonnegative weights under which a record and a hidden part are uncorrelated
decorrelates them up to `3 * d`
(`GameTheory.Math.Probability.beliefDecorrelated_of_near_weights`). The
uncorrelation is stated on the unnormalized weights: the weighted sum of a
product times the total weight is the product of the weighted sums. When the
law is itself the normalization of weights close to the uncorrelated ones,
relative to their total, the distance follows from
`GameTheory.Math.Probability.sum_abs_div_sum_sub_div_sum_le`
(`GameTheory.Math.Probability.beliefDecorrelated_of_close_weights`).
-/

noncomputable section

namespace GameTheory.Math.Probability

open Finset

/-- A weighted sum of a function bounded by one, under nonnegative weights of
total one, is bounded by one. -/
private theorem abs_sum_mul_le_one {H : Type*} [Fintype H] {a F : H → ℝ}
    (a_nonneg : ∀ h, 0 ≤ a h) (a_total : ∑ h, a h = 1) (bounded : ∀ h, |F h| ≤ 1) :
    |∑ h, a h * F h| ≤ 1 := by
  calc |∑ h, a h * F h| ≤ ∑ h, |a h * F h| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, a h := sum_le_sum fun h _ => by
        rw [abs_mul, abs_of_nonneg (a_nonneg h)]
        exact mul_le_of_le_one_right (a_nonneg h) (bounded h)
    _ = 1 := a_total

/-- Two weightings within `d` in `ℓ¹` give a function bounded by one weighted
sums within `d`. -/
private theorem abs_sum_mul_sub_sum_mul_le {H : Type*} [Fintype H] {a b F : H → ℝ} {d : ℝ}
    (near : ∑ h, |a h - b h| ≤ d) (bounded : ∀ h, |F h| ≤ 1) :
    |∑ h, a h * F h - ∑ h, b h * F h| ≤ d := by
  rw [← sum_sub_distrib]
  calc |∑ h, (a h * F h - b h * F h)| ≤ ∑ h, |a h * F h - b h * F h| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, |a h - b h| := sum_le_sum fun h _ => by
        rw [← sub_mul, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (bounded h)
    _ ≤ d := near

/-- **Decorrelation near uncorrelated weights.** Let nonnegative weights `v`
of positive total make a record and a hidden part uncorrelated: for all real
functions of each, the weighted sum of their product times the total weight
is the product of their weighted sums. A law within `d` in `ℓ¹` of the
normalized weights decorrelates the record and the hidden part up to
`3 * d`. -/
theorem beliefDecorrelated_of_near_weights {H R T : Type*} [Fintype H] (law : PMF H)
    (record : H → R) (hidden : H → T) (v : H → ℝ) (v_nonneg : ∀ h, 0 ≤ v h)
    (v_pos : 0 < ∑ h, v h)
    (product : ∀ (first : R → ℝ) (second : T → ℝ),
      (∑ h, v h * (first (record h) * second (hidden h))) * ∑ h, v h =
        (∑ h, v h * first (record h)) * ∑ h, v h * second (hidden h))
    {d : ℝ} (near : ∑ h, |(law h).toReal - v h / ∑ k, v k| ≤ d) :
    BeliefDecorrelated law record hidden (3 * d) := by
  intro first second firstBounded secondBounded
  set V := ∑ k, v k with V_def
  set p : H → ℝ := fun h => (law h).toReal with p_def
  set w : H → ℝ := fun h => v h / V with w_def
  have p_nonneg : ∀ h, 0 ≤ p h := fun h => ENNReal.toReal_nonneg
  have p_total : ∑ h, p h = 1 := by
    have one := expect_constant law 1
    rw [expect_eq_sum] at one
    simpa using one
  have w_nonneg : ∀ h, 0 ≤ w h := fun h => div_nonneg (v_nonneg h) v_pos.le
  have w_total : ∑ h, w h = 1 := by
    simp only [w_def, ← sum_div]
    exact div_self v_pos.ne'
  have weighted : ∀ F : H → ℝ, ∑ h, w h * F h = (∑ h, v h * F h) / V := fun F => by
    rw [sum_div]
    exact sum_congr rfl fun h _ => by simp only [w_def]; ring
  have bothBounded : ∀ h, |first (record h) * second (hidden h)| ≤ 1 := fun h => by
    rw [abs_mul]
    exact (mul_le_mul (firstBounded _) (secondBounded _) (abs_nonneg _) zero_le_one).trans
      (le_of_eq (one_mul 1))
  -- Under the normalized weights the covariance vanishes.
  have uncorrelated : ∑ h, w h * (first (record h) * second (hidden h)) =
      (∑ h, w h * first (record h)) * ∑ h, w h * second (hidden h) := by
    rw [weighted, weighted, weighted, div_mul_div_comm, ← product first second,
      mul_div_mul_right _ _ v_pos.ne']
  have nearProduct := abs_sum_mul_sub_sum_mul_le near bothBounded
  have nearFirst := abs_sum_mul_sub_sum_mul_le near fun h => firstBounded (record h)
  have nearSecond := abs_sum_mul_sub_sum_mul_le near fun h => secondBounded (hidden h)
  have firstOne := abs_sum_mul_le_one p_nonneg p_total fun h => firstBounded (record h)
  have secondOne := abs_sum_mul_le_one w_nonneg w_total fun h => secondBounded (hidden h)
  simp only [p_def, w_def] at nearProduct nearFirst nearSecond firstOne secondOne uncorrelated
  rw [expect_eq_sum, expect_eq_sum, expect_eq_sum]
  set Efg := ∑ h, (law h).toReal * (first (record h) * second (hidden h))
  set Ef := ∑ h, (law h).toReal * first (record h)
  set Eg := ∑ h, (law h).toReal * second (hidden h)
  set Wfg := ∑ h, v h / V * (first (record h) * second (hidden h))
  set Wf := ∑ h, v h / V * first (record h)
  set Wg := ∑ h, v h / V * second (hidden h)
  have split : Efg - Ef * Eg = (Efg - Wfg) - Ef * (Eg - Wg) - Wg * (Ef - Wf) := by
    rw [uncorrelated]
    ring
  rw [split]
  calc |(Efg - Wfg) - Ef * (Eg - Wg) - Wg * (Ef - Wf)|
      ≤ |Efg - Wfg| + |Ef * (Eg - Wg)| + |Wg * (Ef - Wf)| := by
        linarith [abs_sub (Efg - Wfg - Ef * (Eg - Wg)) (Wg * (Ef - Wf)),
          abs_sub (Efg - Wfg) (Ef * (Eg - Wg))]
    _ ≤ d + 1 * d + 1 * d := by
        rw [abs_mul, abs_mul]
        gcongr
    _ = 3 * d := by ring

/-- **Decorrelation of a normalized weighting close to uncorrelated weights.**
Let a law be the normalization of weights `u`, and let nonnegative weights `v`
of positive total make a record and a hidden part uncorrelated, as in
`GameTheory.Math.Probability.beliefDecorrelated_of_near_weights`. If `u` is
within `γ` times the total of `v` of `v` in `ℓ¹`, and the total of `u` is at
least `l > 0` times the total of `v`, then the law decorrelates the record and
the hidden part up to `3 * (2 * γ / l)`. -/
theorem beliefDecorrelated_of_close_weights {H R T : Type*} [Fintype H] (law : PMF H)
    (record : H → R) (hidden : H → T) (u : H → ℝ)
    (law_eq : ∀ h, (law h).toReal = u h / ∑ k, u k) (v : H → ℝ) (v_nonneg : ∀ h, 0 ≤ v h)
    (v_pos : 0 < ∑ h, v h)
    (product : ∀ (first : R → ℝ) (second : T → ℝ),
      (∑ h, v h * (first (record h) * second (hidden h))) * ∑ h, v h =
        (∑ h, v h * first (record h)) * ∑ h, v h * second (hidden h))
    {γ l : ℝ} (close : ∑ h, |u h - v h| ≤ γ * ∑ h, v h) (l_pos : 0 < l)
    (lower : l * ∑ h, v h ≤ ∑ h, u h) :
    BeliefDecorrelated law record hidden (3 * (2 * γ / l)) := by
  refine beliefDecorrelated_of_near_weights law record hidden v v_nonneg v_pos product ?_
  simp only [law_eq]
  exact sum_abs_div_sum_sub_div_sum_le v_nonneg v_pos close l_pos lower

end GameTheory.Math.Probability
