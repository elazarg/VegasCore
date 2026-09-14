/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-! # Finite products and bounded charges -/

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

namespace Finset

/-- A finite set of natural indices with span at most `delay` has at most
`delay + 1` elements. The premise need only compare ordered pairs in the set. -/
theorem card_le_of_bounded_span (indices : Finset Nat) (delay : Nat)
    (hspan : ∀ left ∈ indices, ∀ right ∈ indices, left ≤ right → right ≤ left + delay) :
    indices.card ≤ delay + 1 := by
  classical
  by_cases hnonempty : indices.Nonempty
  · let first := indices.min' hnonempty
    have hfirst : first ∈ indices := Finset.min'_mem indices hnonempty
    have hsubset : indices ⊆ Finset.Icc first (first + delay) := by
      intro index hindex
      have hle : first ≤ index := Finset.min'_le indices index hindex
      exact Finset.mem_Icc.mpr ⟨hle, hspan first hfirst index hindex hle⟩
    have hcard := Finset.card_le_card hsubset
    rw [Nat.card_Icc] at hcard
    omega
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty] using
      Nat.zero_le (delay + 1)

/-- Charge each index to one of `bound` sites and to one of two phases.
The first phase occurs at most once per site; indices in the second phase
have span at most `delay` per site. No disjointness premise is required. -/
theorem card_le_of_bounded_charges (indices : Finset Nat) (selected : Nat → Nat)
    (bound delay : Nat) (first second : Nat → Nat → Prop)
    (hbound : ∀ index ∈ indices, selected index < bound)
    (hphase : ∀ index ∈ indices, first (selected index) index ∨ second (selected index) index)
    (hfirst : ∀ site < bound, ∀ left ∈ indices, ∀ right ∈ indices,
      first site left → first site right → left = right)
    (hsecond : ∀ site < bound, ∀ left ∈ indices, ∀ right ∈ indices,
      second site left → second site right → left ≤ right → right ≤ left + delay) :
    indices.card ≤ bound * (delay + 2) := by
  classical
  have hfiber : ∀ site ∈ Finset.range bound,
      (indices.filter (fun index => selected index = site)).card ≤ delay + 2 := by
    intro site hsite
    let fiber := indices.filter (fun index => selected index = site)
    let initial := fiber.filter (first site)
    let repeated := fiber.filter (fun index => ¬ first site index)
    have hfirstCount : initial.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro left hleft right hright
      exact hfirst site (Finset.mem_range.mp hsite)
        left (Finset.mem_filter.mp (Finset.mem_filter.mp hleft).1).1
        right (Finset.mem_filter.mp (Finset.mem_filter.mp hright).1).1
        (Finset.mem_filter.mp hleft).2 (Finset.mem_filter.mp hright).2
    have hrepeat (index : Nat) (hindex : index ∈ repeated) :
        index ∈ indices ∧ second site index := by
      obtain ⟨hfiber, hnot⟩ := Finset.mem_filter.mp hindex
      obtain ⟨hindex, hselected⟩ := Finset.mem_filter.mp hfiber
      refine ⟨hindex, ?_⟩
      have h := hphase index hindex
      rw [hselected] at h
      exact h.resolve_left hnot
    have hsecondCount : repeated.card ≤ delay + 1 := by
      apply card_le_of_bounded_span
      intro left hleft right hright hle
      exact hsecond site (Finset.mem_range.mp hsite) left (hrepeat left hleft).1
        right (hrepeat right hright).1 (hrepeat left hleft).2 (hrepeat right hright).2 hle
    have hsplit : initial.card + repeated.card = fiber.card :=
      fiber.card_filter_add_card_filter_not _
    change fiber.card ≤ delay + 2
    omega
  have htotal := Finset.card_le_mul_card_image_of_maps_to
    (f := selected) (s := indices) (t := Finset.range bound)
    (fun index hindex => Finset.mem_range.mpr (hbound index hindex)) (delay + 2) hfiber
  simpa only [Finset.card_range, Nat.mul_comm] using htotal

end Finset
