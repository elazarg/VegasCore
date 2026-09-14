/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Products under single-coordinate activation -/

namespace Finset

variable {ι M : Type*} [DecidableEq ι] [CommMonoid M]

/-- Activating one coordinate multiplies a selected product by its factor
when tracked. Coordinates outside the finite set have no effect. -/
theorem prod_ite_of_single_activation (tracked : Finset ι) (factor : ι → M)
    (before after : ι → Bool) (key : ι)
    (hbefore : before key = false) (hafter : after key = true)
    (hother : ∀ other, other ≠ key → after other = before other) :
    (∏ other ∈ tracked, if after other then factor other else 1) =
      (∏ other ∈ tracked, if before other then factor other else 1) *
        if key ∈ tracked then factor key else 1 := by
  classical
  by_cases hmem : key ∈ tracked
  · rw [if_pos hmem, ← mul_prod_erase tracked _ hmem,
      ← mul_prod_erase tracked (fun other => if before other then factor other else 1) hmem]
    simp only [hafter, ↓reduceIte, hbefore, Bool.false_eq_true, one_mul]
    rw [mul_comm]
    congr 1
    apply prod_congr rfl
    intro other hotherMem
    rw [hother other (mem_erase.mp hotherMem).1]
  · rw [if_neg hmem, mul_one]
    apply prod_congr rfl
    intro other hotherMem
    rw [hother other (fun heq => hmem (heq ▸ hotherMem))]

end Finset
