/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Math.Probability.FinDist
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Exact finite probability syntax

Game semantics uses `FinDist` directly. `RationalLaw` is syntax data for an
explicit finite probability table: it retains exact rational masses for
execution backends while its normalization proof ensures that construction can
never produce a partial or malformed semantic law.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability

/-- An explicitly enumerated probability law with exact rational masses.
Repeated values are permitted; their masses combine under `denote`. -/
structure RationalLaw (α : Type) where
  entries : List (α × ℚ≥0)
  normalized : (entries.map Prod.snd).sum = 1

namespace RationalLaw

variable {α : Type}

private theorem cast_sum (weights : List ℚ≥0) :
    ((weights.sum : ℚ≥0) : ℝ) =
      (List.map (fun weight : ℚ≥0 => (weight : ℝ)) weights).sum := by
  induction weights with
  | nil => simp
  | cons head tail ih =>
      simp only [List.sum_cons, List.map_cons, NNRat.cast_add, ih]

theorem indexed_mass_sum (law : RationalLaw α) :
    ∑ index : Fin law.entries.length,
        ((law.entries.get index).2 : ℝ) = 1 := by
  rw [← List.sum_ofFn]
  have hcast := congrArg (fun weight : ℚ≥0 => (weight : ℝ)) law.normalized
  rw [cast_sum] at hcast
  rw [show
      List.ofFn
          (fun index : Fin law.entries.length =>
            ((law.entries.get index).2 : ℝ)) =
        List.map (fun entry : α × ℚ≥0 => (entry.2 : ℝ)) law.entries by
      change
        List.ofFn
            ((fun entry : α × ℚ≥0 => (entry.2 : ℝ)) ∘ law.entries.get) = _
      rw [← List.map_ofFn, List.ofFn_get]]
  simpa [List.map_map, Function.comp_def] using hcast

/-- The exact law on table-entry indices.  This is the canonical policy for a
trusted oracle: the runtime receives an index and deterministically reads the
corresponding value from the retained table. -/
def indexLaw (law : RationalLaw α) : FinDist (Fin law.entries.length) :=
  FinDist.ofWeights
    (fun index : Fin law.entries.length =>
      ((law.entries.get index).2 : ℝ))
    (fun _ => by positivity)
    law.indexed_mass_sum

/-- Read the value named by one retained table entry. -/
def entryValue (law : RationalLaw α) (index : Fin law.entries.length) : α :=
  (law.entries.get index).1

/-- Interpret an exact rational table as GameTheory's canonical finite law.
The finite index carrier makes this work even when `α` is infinite. -/
def denote (law : RationalLaw α) : FinDist α :=
  law.indexLaw.map law.entryValue

@[simp] theorem map_entryValue_indexLaw (law : RationalLaw α) :
    law.indexLaw.map law.entryValue = law.denote := rfl

/-- The probability of a value is the sum of the exact table entries that
name it. Repeated entries therefore combine rather than overwrite. -/
theorem prob_denote [DecidableEq α] (law : RationalLaw α) (value : α) :
    law.denote.prob value =
      ∑ index : Fin law.entries.length,
        if value = (law.entries.get index).1 then
          ((law.entries.get index).2 : ℝ)
        else 0 := by
  unfold denote
  rw [FinDist.prob_map, FinDist.expect_eq_sum]
  apply Finset.sum_congr rfl
  intro index _
  unfold indexLaw entryValue
  rw [FinDist.prob_ofWeights]
  by_cases heq : value = (law.entries.get index).1
  · simp [heq]
  · simp

/-- The point law as exact syntax. -/
def pure (value : α) : RationalLaw α where
  entries := [(value, 1)]
  normalized := by simp

end RationalLaw

end Vegas
