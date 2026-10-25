/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.ProductTransport

/-! # Normalized laws with a common base law

Two finite weight vectors are normalized into laws. Each splits into a regular
part, within relative error `ε` of a positive multiple of a base weight, and an
irregular part of total at most `ρ` times the regular total. If the normalized
regular base weights give a payoff of a record with values in `[0, 1]` the same
expectation on both sides, the two normalized laws give it expectations within
`2 ρ / (1 + ρ) + 2 ε / (1 - ε)`
(`GameTheory.Math.Probability.abs_normalized_sub_le_of_base_agree`). The
multiples on the two sides need not agree: normalization cancels them. A
bijection between the regular parts that keeps the base weight and the record
gives the agreement; it may exchange any coordinates the record and the base
weight do not read, such as one player's hidden values or the other players'
hidden values. The agreement also holds with correlated priors, where no
weight-preserving bijection exists.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Finset

variable {R : Type*}

/-- A unit payoff moves by at most the `ℓ¹` distance for arbitrary weights,
without any assumption that their totals agree. -/
theorem abs_sum_mul_sub_le_sum_abs {α : Type*} [Fintype α] (p q payoff : α → ℝ)
    (unit : ∀ a, 0 ≤ payoff a ∧ payoff a ≤ 1) :
    |∑ a, p a * payoff a - ∑ a, q a * payoff a| ≤ ∑ a, |p a - q a| := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
  rw [← sub_mul, abs_mul, abs_of_nonneg (unit a).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (unit a).2

/-- On equal-mass weights, a unit payoff moves by at most half the `ℓ¹`
distance. The weights themselves may be signed. -/
theorem abs_sum_mul_sub_le_half_sum_abs {α : Type*} [Fintype α] (p q payoff : α → ℝ)
    (mass : ∑ a, p a = ∑ a, q a)
    (unit : ∀ a, 0 ≤ payoff a ∧ payoff a ≤ 1) :
    |∑ a, p a * payoff a - ∑ a, q a * payoff a| ≤ (∑ a, |p a - q a|) / 2 := by
  have centered : ∑ a, p a * payoff a - ∑ a, q a * payoff a =
      ∑ a, (p a - q a) * (payoff a - 1 / 2) := by
    rw [← sum_sub_distrib]
    calc
      _ = ∑ a, ((p a - q a) * (payoff a - 1 / 2) + (p a - q a) / 2) := by
        apply sum_congr rfl
        intro a _
        ring
      _ = _ := by
        rw [sum_add_distrib, ← sum_div, sum_sub_distrib, mass, sub_self, zero_div, add_zero]
  rw [centered]
  calc
    _ ≤ ∑ a, |(p a - q a) * (payoff a - 1 / 2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |p a - q a| / 2 := by
      apply sum_le_sum
      intro a _
      have interval : |payoff a - 1 / 2| ≤ 1 / 2 :=
        abs_le.mpr ⟨by linarith [(unit a).1], by linarith [(unit a).2]⟩
      rw [abs_mul]
      calc
        _ ≤ |p a - q a| * (1 / 2) :=
          mul_le_mul_of_nonneg_left interval (abs_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [sum_div]

open Classical in
/-- One side of a swap: the normalized weight is within `ρ / (1 + ρ) + ε / (1 - ε)` of
the normalized base law on unit payoffs. -/
theorem abs_normalized_sub_base_le {γ : Type*} [Fintype γ] (weight base : γ → ℝ)
    (regular : γ → Prop) (record : γ → R) (scale ε ρ : ℝ) (ε_lt : ε < 1)
    (scale_pos : 0 < scale) (weight_nonneg : ∀ a, 0 ≤ weight a)
    (base_nonneg : ∀ a, regular a → 0 ≤ base a)
    (close : ∀ a, regular a → |weight a - scale * base a| ≤ ε * (scale * base a))
    (positive : 0 < (∑ a, if regular a then base a else 0))
    (irregular : ∑ a, (if regular a then 0 else weight a) ≤
      ρ * ∑ a, (if regular a then weight a else 0))
    (payoff : R → ℝ) (unit : ∀ r, 0 ≤ payoff r ∧ payoff r ≤ 1) :
    |∑ a, weight a / (∑ c, weight c) * payoff (record a) -
      ∑ a, (if regular a then base a else 0) / (∑ c, if regular c then base c else 0) *
        payoff (record a)| ≤ ρ / (1 + ρ) + ε / (1 - ε) := by
  set regularWeight : γ → ℝ := fun a => if regular a then weight a else 0
  set irregularWeight : γ → ℝ := fun a => if regular a then 0 else weight a
  set scaledBase : γ → ℝ := fun a => if regular a then scale * base a else 0
  have scaledBase_nonneg : ∀ a, 0 ≤ scaledBase a := fun a => by
    simp only [scaledBase]
    split
    · exact mul_nonneg scale_pos.le (base_nonneg a (by assumption))
    · exact le_rfl
  have scaledTotal : ∑ a, scaledBase a = scale * ∑ a, if regular a then base a else 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by simp only [scaledBase]; split <;> simp
  have scaledPos : 0 < ∑ a, scaledBase a := by
    rw [scaledTotal]
    exact mul_pos scale_pos positive
  have pointClose : ∀ a, |regularWeight a - scaledBase a| ≤ ε * scaledBase a := fun a => by
    simp only [regularWeight, scaledBase]
    split
    · exact close a (by assumption)
    · simp
  have closeSum : ∑ a, |regularWeight a - scaledBase a| ≤ ε * ∑ a, scaledBase a := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => pointClose a
  have lowerSum : (1 - ε) * ∑ a, scaledBase a ≤ ∑ a, regularWeight a := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have := (abs_le.mp (pointClose a)).1
    linarith
  have regularPos : 0 < ∑ a, regularWeight a :=
    lt_of_lt_of_le (mul_pos (by linarith) scaledPos) lowerSum
  have regular_nonneg : ∀ a, 0 ≤ regularWeight a := fun a => by
    simp only [regularWeight]
    split
    · exact weight_nonneg a
    · exact le_rfl
  have irregular_nonneg : ∀ a, 0 ≤ irregularWeight a := fun a => by
    simp only [irregularWeight]
    split
    · exact le_rfl
    · exact weight_nonneg a
  have split : ∀ a, regularWeight a + irregularWeight a = weight a := fun a => by
    simp only [regularWeight, irregularWeight]
    split <;> simp
  have weightPos : 0 < ∑ a, weight a := lt_of_lt_of_le regularPos
    (sum_le_sum fun a _ => by rw [← split a]; exact le_add_of_nonneg_right (irregular_nonneg a))
  have normalizedMass (f : γ → ℝ) (nonzero : (∑ a, f a) ≠ 0) :
      (∑ a, f a / ∑ c, f c) = 1 := by rw [← sum_div, div_self nonzero]
  have stepIrregular := sum_abs_div_sum_add_sub_div_sum_le regular_nonneg irregular_nonneg
    regularPos irregular
  simp only [split] at stepIrregular
  have stepClose := sum_abs_div_sum_sub_div_sum_le scaledBase_nonneg scaledPos closeSum
    (by linarith) lowerSum
  have normalized : ∀ a, scaledBase a / ∑ c, scaledBase c =
      (if regular a then base a else 0) / ∑ c, if regular c then base c else 0 := fun a => by
    rw [scaledTotal]
    simp only [scaledBase]
    split
    · field_simp
    · simp
  simp only [normalized] at stepClose
  have first := abs_sum_mul_sub_le_half_sum_abs (fun a => weight a / ∑ c, weight c)
    (fun a => regularWeight a / ∑ c, regularWeight c) (fun a => payoff (record a))
    (by rw [normalizedMass _ weightPos.ne', normalizedMass _ regularPos.ne'])
    (fun a => unit _)
  have second := abs_sum_mul_sub_le_half_sum_abs (fun a => regularWeight a / ∑ c, regularWeight c)
    (fun a => (if regular a then base a else 0) / ∑ c, if regular c then base c else 0)
    (fun a => payoff (record a))
    (by rw [normalizedMass _ regularPos.ne', normalizedMass _ positive.ne']) (fun a => unit _)
  have total := abs_sub_le (∑ a, weight a / (∑ c, weight c) * payoff (record a))
    (∑ a, regularWeight a / (∑ c, regularWeight c) * payoff (record a))
    (∑ a, (if regular a then base a else 0) / (∑ c, if regular c then base c else 0) *
      payoff (record a))
  have firstBound := first.trans (div_le_div_of_nonneg_right stepIrregular
    (by norm_num : (0 : ℝ) ≤ 2))
  have secondBound := second.trans (div_le_div_of_nonneg_right stepClose
    (by norm_num : (0 : ℝ) ≤ 2))
  exact total.trans ((add_le_add firstBound secondBound).trans_eq (by ring))

open Classical in
/-- **Normalized laws with a common base law.** If the normalized regular base
weights of two sides give every unit payoff of the record the same expectation,
the normalized weights give it expectations within
`2 ρ / (1 + ρ) + 2 ε / (1 - ε)`. -/
theorem abs_normalized_sub_le_of_base_agree {α β : Type*} [Fintype α] [Fintype β]
    (weight₁ : α → ℝ) (weight₂ : β → ℝ) (base₁ : α → ℝ) (base₂ : β → ℝ)
    (regular₁ : α → Prop) (regular₂ : β → Prop) (record₁ : α → R) (record₂ : β → R)
    (weight₁_nonneg : ∀ a, 0 ≤ weight₁ a) (weight₂_nonneg : ∀ b, 0 ≤ weight₂ b)
    (base₁_nonneg : ∀ a, regular₁ a → 0 ≤ base₁ a)
    (base₂_nonneg : ∀ b, regular₂ b → 0 ≤ base₂ b)
    (scale₁ scale₂ : ℝ) (scale₁_pos : 0 < scale₁) (scale₂_pos : 0 < scale₂)
    (ε ρ : ℝ) (ε_lt : ε < 1)
    (close₁ : ∀ a, regular₁ a → |weight₁ a - scale₁ * base₁ a| ≤ ε * (scale₁ * base₁ a))
    (close₂ : ∀ b, regular₂ b → |weight₂ b - scale₂ * base₂ b| ≤ ε * (scale₂ * base₂ b))
    (base₁_pos : 0 < ∑ a, if regular₁ a then base₁ a else 0)
    (base₂_pos : 0 < ∑ b, if regular₂ b then base₂ b else 0)
    (irregular₁ : ∑ a, (if regular₁ a then 0 else weight₁ a) ≤
      ρ * ∑ a, if regular₁ a then weight₁ a else 0)
    (irregular₂ : ∑ b, (if regular₂ b then 0 else weight₂ b) ≤
      ρ * ∑ b, if regular₂ b then weight₂ b else 0)
    (payoff : R → ℝ) (unit : ∀ r, 0 ≤ payoff r ∧ payoff r ≤ 1)
    (agree : (∑ b, (if regular₂ b then base₂ b else 0) /
      (∑ c, if regular₂ c then base₂ c else 0) * payoff (record₂ b)) =
      ∑ a, (if regular₁ a then base₁ a else 0) /
        (∑ c, if regular₁ c then base₁ c else 0) * payoff (record₁ a)) :
    |∑ a, weight₁ a / (∑ c, weight₁ c) * payoff (record₁ a) -
        ∑ b, weight₂ b / (∑ c, weight₂ c) * payoff (record₂ b)| ≤
      2 * ρ / (1 + ρ) + 2 * ε / (1 - ε) := by
  have one := abs_normalized_sub_base_le weight₁ base₁ regular₁ record₁ scale₁ ε ρ ε_lt
    scale₁_pos weight₁_nonneg base₁_nonneg close₁ base₁_pos irregular₁ payoff unit
  have two := abs_normalized_sub_base_le weight₂ base₂ regular₂ record₂ scale₂ ε ρ ε_lt
    scale₂_pos weight₂_nonneg base₂_nonneg close₂ base₂_pos irregular₂ payoff unit
  rw [agree] at two
  have doubled : 2 * ρ / (1 + ρ) + 2 * ε / (1 - ε) =
      2 * (ρ / (1 + ρ) + ε / (1 - ε)) := by ring
  rw [doubled]
  rw [abs_le] at one two ⊢
  constructor <;> linarith [one.1, one.2, two.1, two.2]

end GameTheory.Math.Probability
