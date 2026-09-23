/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Finite-support composition and branch laws -/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α β : Type*}

theorem map_mix (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (first second : FinDist α) (observe : α → β) :
    (mix weight nonnegative atMostOne first second).map observe =
      mix weight nonnegative atMostOne (first.map observe) (second.map observe) := by
  rw [map_eq_bind, mix_bind]
  rfl

/-- Support-dependent binds transport across equality of their source laws
when corresponding branches agree. -/
theorem bindOnSupport_congr_measure {μ ν : FinDist α} (same : μ = ν)
    (f : ∀ a ∈ μ.support, FinDist β) (g : ∀ a ∈ ν.support, FinDist β)
    (agree : ∀ a ha hb, f a ha = g a hb) :
    μ.bindOnSupport f = ν.bindOnSupport g := by
  subst ν
  apply bindOnSupport_congr
  intro a ha
  exact agree a ha ha

/-- Retype a law whose entire support satisfies a predicate. This does not
condition or renormalize the law. -/
def toSubtype (law : FinDist α) {P : α → Prop}
    (supported : ∀ value ∈ law.support, P value) : FinDist {value // P value} :=
  law.bindOnSupport fun value member => FinDist.pure ⟨value, supported value member⟩

@[simp] theorem map_val_toSubtype (law : FinDist α) {P : α → Prop}
    (supported : ∀ value ∈ law.support, P value) :
    (law.toSubtype supported).map Subtype.val = law := by
  simp only [toSubtype, map_bindOnSupport, map_pure]
  rw [bindOnSupport_eq_bind, bind_pure]

theorem map_toSubtype (law : FinDist α) {P : α → Prop}
    (supported : ∀ value ∈ law.support, P value) (f : α → β) :
    (law.toSubtype supported).map (fun value => f value.1) = law.map f := by
  change (law.toSubtype supported).map (f ∘ Subtype.val) = law.map f
  rw [← map_comp, map_val_toSubtype]

/-- A uniform law on distinct members of a nonempty finite set. -/
def uniformSet (members : Finset α) (nonempty : members.Nonempty) : FinDist α := by
  letI : Nonempty {value // value ∈ members} :=
    ⟨⟨nonempty.choose, nonempty.choose_spec⟩⟩
  exact (uniformOfFintype : FinDist {value // value ∈ members}).map Subtype.val

theorem prob_uniformSet [DecidableEq α] (members : Finset α) (nonempty : members.Nonempty)
    (value : α) :
    (uniformSet members nonempty).prob value =
      if value ∈ members then (members.card : ℝ)⁻¹ else 0 := by
  let : Nonempty {value // value ∈ members} :=
    ⟨⟨nonempty.choose, nonempty.choose_spec⟩⟩
  by_cases member : value ∈ members
  · change ((uniformOfFintype : FinDist {value // value ∈ members}).map Subtype.val).prob
      (Subtype.val ⟨value, member⟩) = _
    rw [prob_map_of_injective Subtype.val Subtype.val_injective]
    simp only [prob_uniformOfFintype, Fintype.card_coe, member, ↓reduceIte]
  · rw [uniformSet, prob_map]
    have absent : (fun old : {value // value ∈ members} =>
        if value = old.val then (1 : ℝ) else 0) = fun _ => 0 := by
      funext old
      apply ite_eq_right
      intro same
      exact member (by rw [same]; exact old.property)
    rw [absent, expect_const, ite_eq_right member]

/-- Adding one distinct candidate scales every old candidate equally. -/
theorem uniformSet_insert [DecidableEq α] (members : Finset α)
    (nonempty : members.Nonempty) (fresh : α) (absent : fresh ∉ members) :
    uniformSet (insert fresh members) (Finset.insert_nonempty fresh members) =
      mix ((members.card : ℝ) + 1)⁻¹
        (inv_nonneg.mpr (by positivity))
        (by rw [inv_le_one₀ (by positivity)]; have := Nat.cast_nonneg (α := ℝ) members.card;
            linarith)
        (pure fresh) (uniformSet members nonempty) := by
  have positive : (0 : ℝ) < members.card := by exact_mod_cast nonempty.card_pos
  apply ext_of_prob
  intro value
  by_cases same : value = fresh
  · subst value
    simp only [prob_uniformSet, Finset.mem_insert_self, ↓reduceIte,
      Finset.card_insert_of_notMem absent, Nat.cast_add, Nat.cast_one, prob_mix,
      prob_pure_self, absent, mul_one, mul_zero, add_zero]
  · by_cases member : value ∈ members
    · simp only [prob_uniformSet, Finset.mem_insert, same, member, or_true,
        ↓reduceIte, Finset.card_insert_of_notMem absent, Nat.cast_add, Nat.cast_one,
        prob_mix, prob_pure_of_ne same, mul_zero, zero_add]
      field_simp
      ring
    · simp only [prob_uniformSet, Finset.mem_insert, same, member, or_self,
        ↓reduceIte, prob_mix, prob_pure_of_ne same, mul_zero, add_zero]

end GameTheory.Math.Probability.FinDist
