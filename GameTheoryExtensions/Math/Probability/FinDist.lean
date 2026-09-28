/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Finite-support composition and branch laws -/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α β : Type*}

/-- A finite-support law can give every point positive probability only on a
finite carrier. A finite time horizon alone does not provide this premise. -/
theorem FullSupport.finite {law : FinDist α} (full : law.FullSupport) : Finite α := by
  have finiteUniv : (Set.univ : Set α).Finite :=
    law.support_finite.subset (fun value _ => full value)
  exact Set.finite_univ_iff.mp finiteUniv

/-- Sample the first coordinate, then the conditional second coordinate.
The conditional law is total, including first coordinates of zero probability. -/
theorem eq_bind_fst_conditional_snd (law : FinDist (α × β)) :
    law = (law.map Prod.fst).bind fun first =>
      ((law.condOnFibre Prod.fst first).map Prod.snd).map (fun second => (first, second)) := by
  classical
  conv_lhs => rw [law.eq_bind_condOnFibre Prod.fst]
  apply bind_congr
  intro first supported
  rw [map_comp]
  symm
  calc
    _ = (law.condOnFibre Prod.fst first).map id := by
      apply map_congr_of_eq_on_support
      intro pair member
      obtain ⟨witness, present, firstEq⟩ := support_map .. ▸ supported
      have meets : ∃ pair ∈ Prod.fst ⁻¹' {first}, pair ∈ law.support :=
        ⟨witness, firstEq, present⟩
      rw [condOnFibre, dite_eq_left meets] at member
      have coordinate := (support_condOn _ _ _ member).1
      exact Prod.ext coordinate.symm rfl
    _ = _ := map_id _

/-- Observing one independent coordinate leaves the other law unchanged.
This also respects the existing fallback at an impossible observation. -/
theorem conditional_snd_product (first : FinDist α) (second : FinDist β) (observed : α) :
    ((product first second).condOnFibre Prod.fst observed).map Prod.snd = second := by
  classical
  unfold condOnFibre
  split
  · rename_i meets
    have positive : 0 < first.prob observed := by
      apply prob_pos_iff.mpr
      rw [← map_fst_product first second, support_map]
      obtain ⟨pair, same, supported⟩ := meets
      exact ⟨pair, supported, same⟩
    have total : (product first second).probOf (Prod.fst ⁻¹' {observed}) =
        first.prob observed := by
      rw [← prob_map_eq_probOf_preimage_singleton, map_fst_product]
    have conditional : (product first second).condOn (Prod.fst ⁻¹' {observed}) meets =
        product (pure observed) second := by
      apply ext_of_prob
      rintro ⟨left, right⟩
      rw [prob_condOn, total, prob_product, prob_product, prob_pure_eq_ite]
      change (if left = observed then first.prob left * second.prob right /
        first.prob observed else 0) =
          (if left = observed then 1 else 0) * second.prob right
      by_cases same : left = observed
      · subst left
        simp only [↓reduceIte, one_mul]
        exact mul_div_cancel_left₀ _ (ne_of_gt positive)
      · simp only [same, ↓reduceIte, zero_mul]
    rw [conditional, map_snd_product]
  · exact map_snd_product first second

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

theorem mem_support_uniformSet_iff (members : Finset α)
    (nonempty : members.Nonempty) (value : α) :
    value ∈ (uniformSet members nonempty).support ↔ value ∈ members := by
  classical
  rw [← prob_pos_iff, prob_uniformSet]
  by_cases member : value ∈ members
  · simp only [member, ↓reduceIte, iff_true]
    exact inv_pos.mpr (by exact_mod_cast nonempty.card_pos)
  · simp [member]

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

/-- Iterating a kernel after an initial bind is the bind of the iterates. -/
theorem iterate_bind (kernel : β → FinDist β) (count : Nat) (law : FinDist α)
    (start : α → FinDist β) :
    (fun distribution => distribution.bind kernel)^[count] (law.bind start) =
      law.bind (fun value => (fun distribution => distribution.bind kernel)^[count]
        (start value)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [Function.iterate_succ_apply', ih, bind_bind]

/-- A point of a nonempty fibre's conditional law lies in the fibre and in the
original support. -/
theorem mem_support_condOnFibre {μ : FinDist α} {f : α → β} {b : β}
    (meets : ∃ a ∈ f ⁻¹' {b}, a ∈ μ.support) {a : α}
    (member : a ∈ (μ.condOnFibre f b).support) : f a = b ∧ a ∈ μ.support := by
  rw [condOnFibre, dite_eq_left meets] at member
  exact support_condOn μ _ meets member

/-- Transporting a law along a type equality maps it by the cast. -/
theorem cast_eq_map_cast {A B : Type _} (same : A = B) (law : FinDist A) :
    cast (congrArg FinDist same) law = law.map (cast same) := by
  cases same
  exact (map_id law).symm

/-- A law whose transport is another law is that law mapped back by the cast. -/
theorem eq_map_cast_of_cast_eq {A B : Type _} (same : A = B) (law : FinDist A)
    (transported : FinDist B) (equal : cast (congrArg FinDist same) law = transported) :
    law = transported.map (cast same.symm) := by
  cases same
  cases equal
  exact (map_id law).symm

/-- Two laws that bind one mixture into the prescribed and alternative laws of
its components have, for every utility, the mixture's average gain as their
gain. -/
theorem expect_sub_eq_of_eq_bind {γ δ : Type*} (mixture : FinDist γ)
    (prescribed alternative : FinDist δ) (componentPrescribed componentAlternative : γ → FinDist δ)
    (prescribedEq : prescribed = mixture.bind componentPrescribed)
    (alternativeEq : alternative = mixture.bind componentAlternative) (utility : δ → ℝ) :
    alternative.expect utility - prescribed.expect utility =
      mixture.expect (fun component =>
        (componentAlternative component).expect utility -
          (componentPrescribed component).expect utility) := by
  rw [prescribedEq, alternativeEq, expect_bind, expect_bind, expect_sub]

end GameTheory.Math.Probability.FinDist
