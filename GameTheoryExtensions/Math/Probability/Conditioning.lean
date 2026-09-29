/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.Joint
import GameTheoryExtensions.Math.Probability.Support

/-! # Total conditioning on a fiber

`fiberConditional μ f b` is the law of `μ` conditioned on the fiber `f = b`.
Unlike `fiberPosterior`, it needs no proof that the fiber has positive mass:
on a null fiber it is `μ` itself, which no bind against the marginal of `f`
ever consults.
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {α β : Type*}

/-- Conditioning on an event rescales the mass of what remains of each event. -/
theorem toOuterMeasure_filter_apply (μ : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ μ.support)
    (t : Set α) :
    (μ.filter s h).toOuterMeasure t = μ.toOuterMeasure (t ∩ s) / μ.toOuterMeasure s := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  by_cases ht : a ∈ t <;> by_cases hs : a ∈ s <;> simp [Set.indicator, ht, hs, PMF.filter_apply]

/-- An event has positive mass exactly when it meets the support. -/
theorem toOuterMeasure_ne_zero_iff (μ : PMF α) (s : Set α) :
    μ.toOuterMeasure s ≠ 0 ↔ ∃ a ∈ s, a ∈ μ.support := by
  rw [ne_eq, PMF.toOuterMeasure_apply_eq_zero_iff, Set.not_disjoint_iff]
  exact ⟨fun ⟨a, supported, member⟩ => ⟨a, member, supported⟩,
    fun ⟨a, member, supported⟩ => ⟨a, supported, member⟩⟩

/-- An event meeting the support has positive real mass. -/
theorem toOuterMeasure_toReal_pos (μ : PMF α) {s : Set α} (meets : ∃ a ∈ s, a ∈ μ.support) :
    0 < (μ.toOuterMeasure s).toReal :=
  ENNReal.toReal_pos ((toOuterMeasure_ne_zero_iff μ s).mpr meets) (outerMeasure_ne_top μ s)

open Classical in
/-- The real mass of a conditioned atom is its share of the event's mass. -/
theorem toReal_filter_apply (μ : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ μ.support) (a : α) :
    ((μ.filter s h) a).toReal =
      if a ∈ s then (μ a).toReal / (μ.toOuterMeasure s).toReal else 0 := by
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
  by_cases member : a ∈ s
  · rw [Set.indicator_of_mem member, ite_eq_left member, div_eq_mul_inv]
  · rw [Set.indicator_of_notMem member, ite_eq_right member, ENNReal.toReal_zero, zero_mul]

/-- The law conditioned on the fiber `f ⁻¹' {b}`, or the law itself when that
fiber has no mass. -/
noncomputable def fiberConditional (μ : PMF α) (f : α → β) (b : β) : PMF α := by
  classical
  exact if meets : ∃ a ∈ f ⁻¹' {b}, a ∈ μ.support then μ.filter (f ⁻¹' {b}) meets else μ

/-- On the support of the marginal, the total conditional is the fiber posterior. -/
theorem fiberConditional_eq_fiberPosterior (μ : PMF α) (f : α → β) {b : β}
    (hb : b ∈ (μ.map f).support) :
    fiberConditional μ f b = fiberPosterior μ f b hb := by
  have meets : ∃ a ∈ f ⁻¹' {b}, a ∈ μ.support := by
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff f μ _).mp hb
    exact ⟨a, rfl, ha⟩
  simp only [fiberConditional, meets, ↓reduceDIte]
  rfl

/-- **Disintegration.** Drawing from a law is drawing its image and then
drawing from the conditional law of that image's fiber. -/
theorem eq_bind_fiberConditional (μ : PMF α) (f : α → β) :
    μ = (μ.map f).bind (fiberConditional μ f) := by
  conv_lhs => rw [← fiberPosterior_reconstruct μ f]
  exact bindOnSupport_eq_bind_of_eq_on_support _ fun _ hb =>
    (fiberConditional_eq_fiberPosterior μ f hb).symm

/-- A point of a nonempty fiber's conditional law lies in the fiber and in the
original support. -/
theorem mem_support_fiberConditional {μ : PMF α} {f : α → β} {b : β}
    (meets : ∃ a ∈ f ⁻¹' {b}, a ∈ μ.support) {a : α}
    (member : a ∈ (fiberConditional μ f b).support) : f a = b ∧ a ∈ μ.support := by
  simp only [fiberConditional, meets, ↓reduceDIte, PMF.mem_support_filter_iff] at member
  exact member

/-- Sample the first coordinate, then the conditional second coordinate.
The conditional law is total, including first coordinates of zero probability. -/
theorem eq_bind_fst_conditional_snd (law : PMF (α × β)) :
    law = (law.map Prod.fst).bind fun first =>
      ((fiberConditional law Prod.fst first).map Prod.snd).map
        (fun second => (first, second)) := by
  conv_lhs => rw [eq_bind_fiberConditional law Prod.fst]
  apply bind_congr_on_support
  intro first supported
  rw [PMF.map_comp]
  symm
  calc
    _ = (fiberConditional law Prod.fst first).map id := by
      apply map_congr_on_support
      intro pair member
      obtain ⟨witness, present, firstEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have meets : ∃ pair ∈ Prod.fst ⁻¹' {first}, pair ∈ law.support :=
        ⟨witness, firstEq, present⟩
      exact Prod.ext (mem_support_fiberConditional meets member).1.symm rfl
    _ = _ := PMF.map_id _

/-- Observing one independent coordinate leaves the other law unchanged.
This also respects the fallback at an impossible observation. -/
theorem conditional_snd_bindPairLaw_const (first : PMF α) (second : PMF β) (observed : α) :
    (fiberConditional (bindPairLaw first fun _ => second) Prod.fst observed).map Prod.snd =
      second := by
  by_cases present : observed ∈ ((bindPairLaw first fun _ => second).map Prod.fst).support
  · rw [fiberConditional_eq_fiberPosterior _ _ present]
    ext right
    rw [fiberPosterior_map_snd_apply, bindPairLaw_apply, bindPairLaw_map_fst]
    rw [bindPairLaw_map_fst] at present
    rw [mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel ((PMF.mem_support_iff _ _).mp present)
      (PMF.apply_ne_top _ _), one_mul]
  · have absent : ¬ ∃ pair ∈ Prod.fst ⁻¹' {observed},
        pair ∈ (bindPairLaw first fun _ => second).support := by
      rintro ⟨pair, same, supported⟩
      exact present ((PMF.mem_support_map_iff _ _ _).mpr ⟨pair, supported, same⟩)
    simp only [fiberConditional, absent, ↓reduceDIte, bindPairLaw_map_snd, PMF.bind_const]

end GameTheory.Math.Probability
