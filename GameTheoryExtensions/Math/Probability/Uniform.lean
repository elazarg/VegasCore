module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Math.Probability.Mixture
public import GameTheory.Math.Probability.Expectation
public import GameTheory.Math.Probability.Uniform
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

/-! # Uniform laws on finite sets -/

noncomputable section

open scoped ENNReal

namespace GameTheory.Math.Probability

variable {α : Type*}

/-- Equal positive mass on a finite nonempty set, and zero elsewhere. -/
def uniformOn (s : Finset α) (nonempty : s.Nonempty) : PMF α := by
  classical
  refine PMF.ofFinset (fun a => if a ∈ s then (s.card : ENNReal)⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr nonempty))
      (ENNReal.natCast_ne_top _)
  · intro a absent
    simp [absent]

open Classical in
/-- Atoms outside the sampling set have zero mass. -/
@[simp] theorem uniformOn_apply (s : Finset α) (nonempty : s.Nonempty) (a : α) :
    uniformOn s nonempty a = if a ∈ s then (s.card : ENNReal)⁻¹ else 0 := by
  classical
  rfl

/-- Each member has inverse-cardinality mass. -/
theorem uniformOn_apply_of_mem {s : Finset α} (nonempty : s.Nonempty)
    {a : α} (member : a ∈ s) : uniformOn s nonempty a = (s.card : ENNReal)⁻¹ := by
  simp [member]

/-- The sampling set is exactly the support. -/
theorem mem_support_uniformOn_iff {s : Finset α} (nonempty : s.Nonempty) (a : α) :
    a ∈ (uniformOn s nonempty).support ↔ a ∈ s := by
  classical
  simp [PMF.mem_support_iff]

open Classical in
/-- An event's mass is the fraction of the sampling set that it contains. -/
theorem uniformOn_toOuterMeasure_apply {s : Finset α} (nonempty : s.Nonempty)
    (event : Set α) :
    (uniformOn s nonempty).toOuterMeasure event =
      ((s.filter (· ∈ event)).card : ENNReal) / s.card := by
  classical
  rw [PMF.toOuterMeasure_apply]
  trans ∑ a ∈ s.filter (· ∈ event), (s.card : ENNReal)⁻¹
  · rw [tsum_eq_sum (s := s.filter (· ∈ event))]
    · apply Finset.sum_congr rfl
      intro a member
      simp only [Finset.mem_filter] at member
      simp [uniformOn_apply, member.1, member.2]
    · intro a absent
      simp only [Finset.mem_filter, not_and] at absent
      by_cases member : a ∈ s
      · simp [absent member]
      · simp [Set.indicator_apply, uniformOn_apply, member]
  · simp [div_eq_mul_inv]

/-- Every point of a finite nonempty carrier has real mass one over its size. -/
theorem toReal_uniformLaw_apply [Fintype α] [Nonempty α] (a : α) :
    ((uniformLaw α) a).toReal = (Fintype.card α : ℝ)⁻¹ := by
  rw [uniformLaw_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- A mixture is supported inside the union of its components' supports. -/
theorem support_mix_subset (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : PMF α) :
    (mix t h0 h1 μ ν).support ⊆ μ.support ∪ ν.support := by
  intro value member
  by_contra neither
  simp only [Set.mem_union, PMF.mem_support_iff, not_or, not_not] at neither
  rw [PMF.mem_support_iff, mix_apply] at member
  simp [neither.1, neither.2] at member

end GameTheory.Math.Probability
