/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.EnforcementLimits
import Mathlib.Data.Finset.Max

/-! # Computing the least scalar sanction

A finite table supplies rational upper gains and nonnegative additional
collection coefficients. The checker rejects exactly a positive gain with
zero additional collection. Otherwise it computes the least nonnegative
deposit satisfying every row, including among real-valued deposits.

This is a decision procedure for the supplied comparison certificate. Failure
does not show that a game has no preserving implementation: the table may
include continuations that no sequential equilibrium needs to use. The
coefficients, monitoring rule, and compared laws are fixed before inference.
-/

namespace GameTheory.Enforcement

open Math.Probability

variable {Index Outcome : Type*}

/-- The largest required ratio, with zero as a lower bound. A zero denominator
contributes zero; `inferScalarDeposit` separately checks those rows. -/
def scalarDeposit (rows : Finset Index) (gain collection : Index → ℚ) : ℚ :=
  (insert 0 (rows.image (fun index => gain index / collection index))).max'
    (Finset.insert_nonempty ..)

/-- Infer a deposit from a table with nonnegative collection coefficients.
The return value is executable; nonnegativity is an explicit soundness premise. -/
def inferScalarDeposit (rows : Finset Index) (gain collection : Index → ℚ) : Option ℚ :=
  if ∀ index ∈ rows, collection index = 0 → gain index ≤ 0 then
    some (scalarDeposit rows gain collection)
  else none

theorem scalarDeposit_nonnegative (rows : Finset Index) (gain collection : Index → ℚ) :
    0 ≤ scalarDeposit rows gain collection := by
  exact Finset.le_max' _ 0 (Finset.mem_insert_self ..)

theorem ratio_le_scalarDeposit (rows : Finset Index) (gain collection : Index → ℚ)
    {index : Index} (member : index ∈ rows) :
    gain index / collection index ≤ scalarDeposit rows gain collection := by
  exact Finset.le_max' _ _
    (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem (fun entry => gain entry / collection entry) member))

theorem scalarDeposit_deters (rows : Finset Index) (gain collection : Index → ℚ)
    (nonnegative : ∀ index ∈ rows, 0 ≤ collection index)
    (undetectable : ∀ index ∈ rows, collection index = 0 → gain index ≤ 0)
    {index : Index} (member : index ∈ rows) :
    gain index ≤ collection index * scalarDeposit rows gain collection := by
  by_cases zero : collection index = 0
  · simpa only [zero, zero_mul] using undetectable index member zero
  · have positive : 0 < collection index :=
      lt_of_le_of_ne (nonnegative index member) (Ne.symm zero)
    exact ((div_le_iff₀ positive).mp
      (ratio_le_scalarDeposit rows gain collection member)).trans_eq (mul_comm ..)

/-- Minimality holds against every feasible nonnegative real deposit, not just
against the rational candidates enumerated by the checker. -/
theorem scalarDeposit_le (rows : Finset Index) (gain collection : Index → ℚ)
    (nonnegative : ∀ index ∈ rows, 0 ≤ collection index)
    {deposit : ℝ} (deposit_nonnegative : 0 ≤ deposit)
    (deters : ∀ index ∈ rows, (gain index : ℝ) ≤ (collection index : ℝ) * deposit) :
    (scalarDeposit rows gain collection : ℝ) ≤ deposit := by
  have member := Finset.max'_mem
    (insert 0 (rows.image (fun index => gain index / collection index)))
    (Finset.insert_nonempty ..)
  change scalarDeposit rows gain collection ∈ _ at member
  rcases Finset.mem_insert.mp member with zero | member
  · simpa only [zero, Rat.cast_zero] using deposit_nonnegative
  · obtain ⟨index, inRows, equal⟩ := Finset.mem_image.mp member
    rw [← equal, Rat.cast_div]
    by_cases zero : collection index = 0
    · simpa only [zero, Rat.cast_zero, div_zero] using deposit_nonnegative
    · have positive : (0 : ℝ) < (collection index : ℝ) := by
        exact_mod_cast lt_of_le_of_ne (nonnegative index inRows) (Ne.symm zero)
      exact (div_le_iff₀ positive).mpr ((deters index inRows).trans_eq (mul_comm ..))

theorem inferScalarDeposit_eq_none_iff (rows : Finset Index)
    (gain collection : Index → ℚ) :
    inferScalarDeposit rows gain collection = none ↔
      ∃ index ∈ rows, collection index = 0 ∧ 0 < gain index := by
  simp only [inferScalarDeposit, ite_eq_right_iff, Option.some_ne_none, imp_false]
  push Not
  rfl

/-- Every returned deposit satisfies the original real inequalities. -/
theorem inferred_deposit_sound (rows : Finset Index) (gain collection : Index → ℚ)
    (nonnegative : ∀ index ∈ rows, 0 ≤ collection index)
    {deposit : ℚ} (inferred : inferScalarDeposit rows gain collection = some deposit) :
    0 ≤ deposit ∧ ∀ index ∈ rows, (gain index : ℝ) ≤ (collection index : ℝ) * deposit := by
  unfold inferScalarDeposit at inferred
  split at inferred
  next safe =>
    cases Option.some.inj inferred
    refine ⟨scalarDeposit_nonnegative .., ?_⟩
    intro index member
    exact_mod_cast scalarDeposit_deters rows gain collection nonnegative safe member
  next => contradiction

theorem inferred_deposit_minimal (rows : Finset Index) (gain collection : Index → ℚ)
    (nonnegative : ∀ index ∈ rows, 0 ≤ collection index)
    {deposit : ℚ} (inferred : inferScalarDeposit rows gain collection = some deposit)
    {other : ℝ} (other_nonnegative : 0 ≤ other)
    (deters : ∀ index ∈ rows, (gain index : ℝ) ≤ (collection index : ℝ) * other) :
    (deposit : ℝ) ≤ other := by
  unfold inferScalarDeposit at inferred
  split at inferred
  next =>
    cases Option.some.inj inferred
    exact scalarDeposit_le rows gain collection nonnegative other_nonnegative deters
  next => contradiction

/-- Rejection supplies an undeterrable row of this certificate. It is not a
statement about other certificates or about equilibrium implementability. -/
theorem rejected_deposit_infeasible (rows : Finset Index) (gain collection : Index → ℚ)
    (rejected : inferScalarDeposit rows gain collection = none) :
    ¬ ∃ deposit : ℝ, ∀ index ∈ rows,
      (gain index : ℝ) ≤ (collection index : ℝ) * deposit := by
  obtain ⟨index, member, zero, profitable⟩ :=
    (inferScalarDeposit_eq_none_iff rows gain collection).mp rejected
  rintro ⟨deposit, deters⟩
  have bound := deters index member
  rw [zero, Rat.cast_zero, zero_mul] at bound
  have positive : (0 : ℝ) < (gain index : ℝ) := by exact_mod_cast profitable
  exact not_le.mpr positive bound

/-- A successfully checked table certifies actual finite-distribution
comparisons when its rational entries bound gain and additional collection. -/
theorem inferred_deposit_holds (rows : Finset Index) (gain collection : Index → ℚ)
    (nonnegative : ∀ index ∈ rows, 0 ≤ collection index)
    {deposit : ℚ} (inferred : inferScalarDeposit rows gain collection = some deposit)
    (comparisons : Index → IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome)
    (gain_bound : ∀ index ∈ rows,
      (comparisons index).alternative.expect base -
        (comparisons index).prescribed.expect base ≤ (gain index : ℝ))
    (collection_bound : ∀ index ∈ rows, (collection index : ℝ) ≤
      (comparisons index).alternative.probOf sanction -
        (comparisons index).prescribed.probOf sanction)
    {index : Index} (member : index ∈ rows) :
    (comparisons index).Holds (sanctionedUtility base sanction deposit) := by
  obtain ⟨nonnegative_deposit, deters⟩ :=
    inferred_deposit_sound rows gain collection nonnegative inferred
  rw [holds_iff_incremental_sanction]
  refine (gain_bound index member).trans ((deters index member).trans ?_)
  apply mul_le_mul_of_nonneg_right (collection_bound index member)
  exact_mod_cast nonnegative_deposit

end GameTheory.Enforcement
