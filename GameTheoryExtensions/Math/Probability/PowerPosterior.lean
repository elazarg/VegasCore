/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.NormalizedPower

/-! # Finite posterior limits from leading powers

One common scale is removed from every weight in a fiber. Terms of strictly
higher order disappear; the remaining positive coefficients normalize to the
complete limiting law.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

variable {A : Type*} [Fintype A]

/-- Leading coefficients at a supplied reference order, with higher orders zeroed. -/
def leadingPowerWeight (coefficient : A → ℝ) (order : A → Nat) (reference : A) (a : A) : ℝ :=
  if order a = order reference then coefficient a else 0

omit [Fintype A] in
theorem leadingPowerWeight_nonneg (coefficient : A → ℝ) (positive : ∀ a, 0 < coefficient a)
    (order : A → Nat) (reference a : A) :
    0 ≤ leadingPowerWeight coefficient order reference a := by
  unfold leadingPowerWeight
  split
  · exact (positive a).le
  · exact le_refl 0

theorem sum_leadingPowerWeight_pos (coefficient : A → ℝ) (positive : ∀ a, 0 < coefficient a)
    (order : A → Nat) (reference : A) :
    0 < ∑ a, leadingPowerWeight coefficient order reference a := by
  have single := Finset.single_le_sum
    (fun a _ => leadingPowerWeight_nonneg coefficient positive order reference a)
    (Finset.mem_univ reference)
  exact lt_of_lt_of_le (by simpa [leadingPowerWeight] using positive reference) single

/-- The explicit finite leading law, rather than an unspecified compactness limit. -/
def leadingPowerLaw (coefficient : A → ℝ) (positive : ∀ a, 0 < coefficient a)
    (order : A → Nat) (reference : A) : PMF A :=
  PMF.ofSimplex (mem_simplexWeights.mpr ⟨fun a =>
    div_nonneg (leadingPowerWeight_nonneg coefficient positive order reference a)
      (sum_leadingPowerWeight_pos coefficient positive order reference).le, by
    rw [← Finset.sum_div,
      div_self (sum_leadingPowerWeight_pos coefficient positive order reference).ne']⟩)

@[simp]
theorem leadingPowerLaw_toReal (coefficient : A → ℝ) (positive : ∀ a, 0 < coefficient a)
    (order : A → Nat) (reference a : A) :
    (leadingPowerLaw coefficient positive order reference a).toReal =
      leadingPowerWeight coefficient order reference a /
        ∑ b, leadingPowerWeight coefficient order reference b :=
  congrFun (PMF.ofSimplex_toReal _) a

/-- Support orders and positive coefficient ratios identify the entire limiting
law, including its zero-probability atoms. -/
theorem leadingPowerLaw_eq_of_ratios (law : PMF A) (coefficient : A → ℝ)
    (positive : ∀ a, 0 < coefficient a) (order : A → Nat) (reference : A)
    (support : ∀ a, order a = order reference ↔ (law a).toReal ≠ 0)
    (ratios : ∀ a, (law a).toReal ≠ 0 →
      coefficient a / coefficient reference = (law a).toReal / (law reference).toReal) :
    leadingPowerLaw coefficient positive order reference = law := by
  have referenceNonzero : (law reference).toReal ≠ 0 := (support reference).mp rfl
  have cross (a : A) :
      leadingPowerWeight coefficient order reference a * (law reference).toReal =
        (law a).toReal * coefficient reference := by
    by_cases nonzero : (law a).toReal ≠ 0
    · rw [leadingPowerWeight, ite_eq_left ((support a).mpr nonzero)]
      exact (div_eq_div_iff (positive reference).ne' referenceNonzero).mp (ratios a nonzero)
    · rw [leadingPowerWeight, ite_eq_right (fun same => nonzero ((support a).mp same)),
        not_not.mp nonzero, zero_mul, zero_mul]
  have total : (∑ a, leadingPowerWeight coefficient order reference a) *
      (law reference).toReal = coefficient reference := by
    rw [Finset.sum_mul]
    simp_rw [cross]
    rw [← Finset.sum_mul, (mem_simplexWeights.mp (PMF.toReal_mem_simplexWeights law)).2,
      one_mul]
  apply pmf_ext_toReal
  intro a
  rw [leadingPowerLaw_toReal]
  apply (div_eq_iff (sum_leadingPowerWeight_pos coefficient positive order reference).ne').mpr
  apply mul_right_cancel₀ referenceNonzero
  rw [cross, ← total]
  ring

/-- Normalized finite weights converge from their leading-power constraints.
No Bayes-convergence premise is used. -/
theorem finite_power_ratio_tendsto (weight : Nat → A → ℝ) (coefficient : A → ℝ)
    (positive : ∀ a, 0 < coefficient a) (order : A → Nat) (reference : A)
    (minimal : ∀ a, order reference ≤ order a)
    {parameter : Nat → ℝ} (parameterPositive : ∀ n, 0 < parameter n)
    (vanishes : Tendsto parameter atTop (nhds 0))
    (leading : ∀ a, Tendsto (fun n => weight n a / parameter n ^ order a) atTop
      (nhds (coefficient a))) (a : A) :
    Tendsto (fun n => weight n a / ∑ b, weight n b) atTop
      (nhds ((leadingPowerLaw coefficient positive order reference a).toReal)) := by
  have scaled (b : A) :
      Tendsto (fun n => weight n b / parameter n ^ order reference) atTop
        (nhds (leadingPowerWeight coefficient order reference b)) := by
    have multiply := (leading b).mul (vanishes.pow (order b - order reference))
    have limit : coefficient b * (0 : ℝ) ^ (order b - order reference) =
        leadingPowerWeight coefficient order reference b := by
      by_cases same : order b = order reference
      · simp [same, leadingPowerWeight]
      · have strict : 0 < order b - order reference := by have := minimal b; omega
        simp [zero_pow strict.ne', leadingPowerWeight, same]
    rw [limit] at multiply
    apply multiply.congr'
    filter_upwards [] with n
    have powers : parameter n ^ order b =
        parameter n ^ (order b - order reference) * parameter n ^ order reference := by
      rw [← pow_add, Nat.sub_add_cancel (minimal b)]
    rw [powers]
    field_simp [ne_of_gt (parameterPositive n)]
  have denominator := tendsto_finsetSum Finset.univ fun b _ => scaled b
  have limit := (scaled a).div denominator
    (sum_leadingPowerWeight_pos coefficient positive order reference).ne'
  rw [leadingPowerLaw_toReal]
  apply limit.congr'
  filter_upwards [] with n
  simp only [Pi.div_def]
  rw [← Finset.sum_div]
  exact (div_div_div_cancel_right₀ (pow_ne_zero _ (ne_of_gt (parameterPositive n)))
    (weight n a) (∑ b, weight n b))

end GameTheory.Math.Probability
