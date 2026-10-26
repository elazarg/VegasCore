/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.Simplex
import GameTheory.Math.Probability.Convergence

/-! # Normalized positive power laws

Finite positive monomial weights define fully supported ordinary PMFs. Their
local denominators have their actual limits; no equality of denominators at
different information states is needed.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

variable {A : Type*} [Fintype A] [Nonempty A]

/-- The actual local normalizer of positive monomial weights. -/
def powerNormalizer (coefficient : A → ℝ) (order : A → Nat) (t : ℝ) : ℝ :=
  ∑ a, coefficient a * t ^ order a

theorem powerNormalizer_pos (coefficient : A → ℝ) (positive : ∀ a, 0 < coefficient a)
    (order : A → Nat) {t : ℝ} (tPositive : 0 < t) :
    0 < powerNormalizer coefficient order t := by
  exact Finset.sum_pos (fun a _ => mul_pos (positive a) (pow_pos tPositive _))
    Finset.univ_nonempty

/-- A finite positive power law, including its own local normalization. -/
def normalizedPower (coefficient : A → ℝ) (positive : ∀ a, 0 < coefficient a)
    (order : A → Nat) (t : ℝ) (tPositive : 0 < t) : PMF A :=
  PMF.ofSimplex (mem_simplexWeights.mpr ⟨fun a =>
    div_nonneg (mul_pos (positive a) (pow_pos tPositive _)).le
      (powerNormalizer_pos coefficient positive order tPositive).le, by
    rw [← Finset.sum_div, ← powerNormalizer,
      div_self (powerNormalizer_pos coefficient positive order tPositive).ne']⟩)

@[simp]
theorem normalizedPower_toReal (coefficient : A → ℝ) (positive : ∀ a, 0 < coefficient a)
    (order : A → Nat) (t : ℝ) (tPositive : 0 < t) (a : A) :
    (normalizedPower coefficient positive order t tPositive a).toReal =
      coefficient a * t ^ order a / powerNormalizer coefficient order t := by
  exact congrFun (PMF.ofSimplex_toReal _) a

theorem normalizedPower_supported (coefficient : A → ℝ) (positive : ∀ a, 0 < coefficient a)
    (order : A → Nat) (t : ℝ) (tPositive : 0 < t) (a : A) :
    a ∈ (normalizedPower coefficient positive order t tPositive).support := by
  apply (PMF.mem_support_iff _ _).mpr
  have realPositive :
      0 < (normalizedPower coefficient positive order t tPositive a).toReal := by
    rw [normalizedPower_toReal]
    exact div_pos (mul_pos (positive a) (pow_pos tPositive _))
      (powerNormalizer_pos coefficient positive order tPositive)
  intro zero
  rw [zero, ENNReal.toReal_zero] at realPositive
  exact (lt_irrefl 0) realPositive

omit [Nonempty A] in
/-- The constant term of each monomial determines the actual denominator limit. -/
theorem powerNormalizer_tendsto (coefficient : A → ℝ) (order : A → Nat)
    {parameter : Nat → ℝ} (vanishes : Tendsto parameter atTop (nhds 0)) :
    Tendsto (fun n => powerNormalizer coefficient order (parameter n)) atTop
      (nhds (∑ a, if order a = 0 then coefficient a else 0)) := by
  apply tendsto_finsetSum Finset.univ
  intro a _
  simpa only [zero_pow_eq, mul_ite, mul_one, mul_zero] using
    (vanishes.pow (order a)).const_mul (coefficient a)

/-- Dividing one actual action probability by its leading power leaves the
coefficient divided by the limiting local normalizer. -/
theorem normalizedPower_scaled_tendsto (coefficient : A → ℝ)
    (positive : ∀ a, 0 < coefficient a) (order : A → Nat)
    {parameter : Nat → ℝ} (parameterPositive : ∀ n, 0 < parameter n)
    (vanishes : Tendsto parameter atTop (nhds 0))
    (constantSum : (∑ a, if order a = 0 then coefficient a else 0) = 1) (a : A) :
    Tendsto (fun n =>
      (normalizedPower coefficient positive order (parameter n) (parameterPositive n) a).toReal /
        parameter n ^ order a) atTop (nhds (coefficient a)) := by
  have denominator := powerNormalizer_tendsto coefficient order vanishes
  rw [constantSum] at denominator
  have limit : Tendsto (fun n => coefficient a / powerNormalizer coefficient order (parameter n))
      atTop (nhds (coefficient a)) := by
    simpa only [div_one, Pi.div_def] using
      (tendsto_const_nhds (x := coefficient a)).div denominator (by norm_num : (1 : ℝ) ≠ 0)
  apply limit.congr'
  filter_upwards [] with n
  rw [normalizedPower_toReal]
  field_simp [ne_of_gt (parameterPositive n)]

/-- Each local law converges to its prescribed finite probability law. -/
theorem normalizedPower_converges (base : PMF A) (coefficient : A → ℝ)
    (positive : ∀ a, 0 < coefficient a) (order : A → Nat)
    (constantTerm : ∀ a, (if order a = 0 then coefficient a else 0) = (base a).toReal)
    {parameter : Nat → ℝ} (parameterPositive : ∀ n, 0 < parameter n)
    (vanishes : Tendsto parameter atTop (nhds 0)) :
    PMFConvergesPointwise
      (fun n => normalizedPower coefficient positive order (parameter n) (parameterPositive n))
      base := by
  have constantSum : (∑ a, if order a = 0 then coefficient a else 0) = 1 := by
    simp_rw [constantTerm]
    exact (mem_simplexWeights.mp (PMF.toReal_mem_simplexWeights base)).2
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro a
  have numerator : Tendsto (fun n => coefficient a * parameter n ^ order a) atTop
      (nhds ((base a).toReal)) := by
    simpa only [zero_pow_eq, mul_ite, mul_one, mul_zero, constantTerm] using
      (vanishes.pow (order a)).const_mul (coefficient a)
  have denominator := powerNormalizer_tendsto coefficient order vanishes
  rw [constantSum] at denominator
  simpa only [div_one, normalizedPower_toReal, Pi.div_def] using
    numerator.div denominator (by norm_num : (1 : ℝ) ≠ 0)

end GameTheory.Math.Probability
