/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.PendingSelection

/-! # Pending selection with a positive probability of selecting nothing

Each distinct eligible identifier receives the same weight. The outside
option has weight one. Adding an identifier changes only its own inclusion
chance and uniformly scales the old law, including the outside option.
-/

noncomputable section

namespace Interaction.MessageNetwork

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]

def inclusionMass (weight : ℝ) (count : ℕ) : ℝ :=
  (count : ℝ) * weight / (1 + (count : ℝ) * weight)

theorem inclusionMass_nonnegative (weight : ℝ) (nonnegative : 0 ≤ weight) (count : ℕ) :
    0 ≤ inclusionMass weight count := by
  unfold inclusionMass
  positivity

theorem inclusionMass_below_one (weight : ℝ) (nonnegative : 0 ≤ weight) (count : ℕ) :
    inclusionMass weight count < 1 := by
  have denominator : 0 < 1 + (count : ℝ) * weight := by positivity
  rw [inclusionMass, div_lt_one denominator]
  linarith

def chooseWithOutside (weight : ℝ) (nonnegative : 0 ≤ weight)
    (candidates : Finset (MessageId Principal)) : PMF (Option (MessageId Principal)) :=
  mix (inclusionMass weight candidates.card)
    (inclusionMass_nonnegative weight nonnegative candidates.card)
    (inclusionMass_below_one weight nonnegative candidates.card).le
    (chooseUniform candidates) (PMF.pure none)

theorem chooseUniform_some_toReal (candidates : Finset (MessageId Principal))
    (id : MessageId Principal) :
    ((chooseUniform candidates) (some id)).toReal =
      if id ∈ candidates then (candidates.card : ℝ)⁻¹ else 0 := by
  classical
  by_cases nonempty : candidates.Nonempty
  · rw [chooseUniform, dite_eq_left nonempty]
    rw [pmf_map_apply_of_injective _ (Option.some_injective _)]
    by_cases member : id ∈ candidates <;>
      simp [PMF.uniformOfFinset_apply, member, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · have empty : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst candidates
    simp [chooseUniform, PMF.pure_apply]

omit [DecidableEq Principal] in
theorem chooseUniform_none (candidates : Finset (MessageId Principal)) :
    (chooseUniform candidates) none = if candidates.Nonempty then 0 else 1 := by
  classical
  by_cases nonempty : candidates.Nonempty
  · rw [chooseUniform, dite_eq_left nonempty, PMF.map_apply]
    simp [Finset.nonempty_iff_ne_empty.mp nonempty]
  · simp [chooseUniform, nonempty, PMF.pure_apply]

theorem chooseWithOutside_some_toReal (weight : ℝ) (nonnegative : 0 ≤ weight)
    (candidates : Finset (MessageId Principal)) (id : MessageId Principal) :
    ((chooseWithOutside weight nonnegative candidates) (some id)).toReal =
      if id ∈ candidates then weight / (1 + (candidates.card : ℝ) * weight) else 0 := by
  rw [chooseWithOutside, mix_apply_toReal, chooseUniform_some_toReal]
  simp only [PMF.pure_apply, Option.some_ne_none, ↓reduceIte,
    ENNReal.toReal_zero, mul_zero, add_zero]
  by_cases member : id ∈ candidates
  · rw [ite_eq_left member, ite_eq_left member, inclusionMass]
    have cardinal : (candidates.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨id, member⟩).ne'
    field_simp
  · simp [member]

omit [DecidableEq Principal] in
theorem chooseWithOutside_none_toReal (weight : ℝ) (nonnegative : 0 ≤ weight)
    (candidates : Finset (MessageId Principal)) :
    ((chooseWithOutside weight nonnegative candidates) none).toReal =
      1 / (1 + (candidates.card : ℝ) * weight) := by
  classical
  rw [chooseWithOutside, mix_apply_toReal, chooseUniform_none]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one, mul_one]
  by_cases nonempty : candidates.Nonempty
  · simp only [nonempty, ↓reduceIte, ENNReal.toReal_zero, mul_zero, zero_add,
      inclusionMass]
    have denominator : 1 + (candidates.card : ℝ) * weight ≠ 0 := by positivity
    field_simp
    ring
  · have empty : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst candidates
    simp [inclusionMass]

/-- Removing an eligible fresh identifier leaves precisely the residual law. -/
theorem chooseWithOutside_insert (weight : ℝ) (nonnegative : 0 ≤ weight)
    (candidates : Finset (MessageId Principal)) (fresh : MessageId Principal)
    (absent : fresh ∉ candidates) :
    chooseWithOutside weight nonnegative (insert fresh candidates) =
      mix (weight / (1 + ((candidates.card : ℝ) + 1) * weight))
        (by positivity)
        (by
          have denominator : 0 < 1 + ((candidates.card : ℝ) + 1) * weight := by positivity
          rw [div_le_one denominator]
          nlinarith [Nat.cast_nonneg (α := ℝ) candidates.card])
        (PMF.pure (some fresh)) (chooseWithOutside weight nonnegative candidates) := by
  classical
  have firstDenominator : 1 + (candidates.card : ℝ) * weight ≠ 0 := by positivity
  have secondDenominator : 1 + ((candidates.card : ℝ) + 1) * weight ≠ 0 := by positivity
  ext value
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    mix_apply_toReal]
  cases value with
  | none =>
      rw [chooseWithOutside_none_toReal, chooseWithOutside_none_toReal]
      simp only [Finset.card_insert_of_notMem absent, Nat.cast_add, Nat.cast_one,
        PMF.pure_apply, reduceCtorEq, ↓reduceIte, ENNReal.toReal_zero, mul_zero, zero_add]
      field_simp
      ring
  | some id =>
      rw [chooseWithOutside_some_toReal, chooseWithOutside_some_toReal]
      simp only [Finset.card_insert_of_notMem absent, Nat.cast_add, Nat.cast_one]
      by_cases same : id = fresh
      · subst id
        simp only [Finset.mem_insert_self, ↓reduceIte, absent, PMF.pure_apply,
          ENNReal.toReal_one, mul_one, mul_zero, add_zero]
      · by_cases member : id ∈ candidates
        · simp only [Finset.mem_insert, same, member, or_true, ↓reduceIte,
            PMF.pure_apply, Option.some.injEq, ENNReal.toReal_zero, mul_zero, zero_add]
          field_simp
          ring
        · simp [same, member, PMF.pure_apply]

omit [DecidableEq Principal] in
/-- A single identifier's inclusion probability can approach one arbitrarily closely. -/
theorem chooseWithOutside_singleton_toReal (weight : ℝ) (nonnegative : 0 ≤ weight)
    (id : MessageId Principal) :
    ((chooseWithOutside weight nonnegative {id}) (some id)).toReal = weight / (1 + weight) := by
  classical
  simp [chooseWithOutside_some_toReal]

omit [DecidableEq Principal] in
/-- Every inclusion probability strictly below one is realized with finite weight. -/
theorem chooseWithOutside_realizes_probability (probability : ℝ)
    (nonnegative : 0 ≤ probability) (belowOne : probability < 1)
    (id : MessageId Principal) :
    ((chooseWithOutside (probability / (1 - probability)) (by positivity) {id})
      (some id)).toReal = probability ∧
      ((chooseWithOutside (probability / (1 - probability)) (by positivity) {id})
        none).toReal = 1 - probability := by
  have denominator : 1 - probability ≠ 0 := by linarith
  have total : 1 + probability / (1 - probability) ≠ 0 := by
    have nonnegativeWeight : 0 ≤ probability / (1 - probability) := by positivity
    linarith
  constructor
  · rw [chooseWithOutside_singleton_toReal]
    field_simp
    ring
  · rw [chooseWithOutside_none_toReal]
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    field_simp
    ring

end Interaction.MessageNetwork
