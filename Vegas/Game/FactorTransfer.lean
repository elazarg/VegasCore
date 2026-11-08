/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.Support

/-! # Moving a factored law to a finer key

A joint law of a key and some traffic factors through a view of the key when
the traffic is noise read from the view. When a finer key is read from the key,
and the view of the key is read back from the view of the finer key on the
support, the joint law of the finer key and the traffic factors through the
view of the finer key.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability

/-- **A factored law moves to a finer key.** -/
theorem factored_of_finer {Final Key Traffic View : Type} (law : PMF Final)
    (coarse fine : Final → Key) (traffic : Final → Traffic) (view : Key → View)
    (noise : View → PMF Traffic)
    (factored : law.map (fun final => (coarse final, traffic final)) =
      (law.map coarse).bind fun current => (noise (view current)).map fun extra =>
        (current, extra))
    (refine : Key → Key) (refines : ∀ final ∈ law.support, fine final = refine (coarse final))
    (reflects : ∀ left ∈ law.support, ∀ right ∈ law.support,
      view (fine left) = view (fine right) → view (coarse left) = view (coarse right)) :
    ∃ fineNoise : View → PMF Traffic,
      law.map (fun final => (fine final, traffic final)) =
        (law.map fine).bind fun current => (fineNoise (view current)).map fun extra =>
          (current, extra) := by
  classical
  obtain ⟨anchor, _⟩ := law.support_nonempty
  let recover := fun observed : View =>
    if found : ∃ final ∈ law.support, view (fine final) = observed then
      view (coarse found.choose) else view (coarse anchor)
  have recovered (final : Final) (member : final ∈ law.support) :
      recover (view (fine final)) = view (coarse final) := by
    have found : ∃ other ∈ law.support, view (fine other) = view (fine final) :=
      ⟨final, member, rfl⟩
    simp only [recover, dite_eq_left found]
    exact reflects _ found.choose_spec.1 final member found.choose_spec.2
  refine ⟨fun observed => noise (recover observed), ?_⟩
  calc law.map (fun final => (fine final, traffic final))
      = (law.map fun final => (coarse final, traffic final)).bind fun pair =>
          PMF.pure (refine pair.1, pair.2) := by
        change _ = PMF.map (fun pair : Key × Traffic => (refine pair.1, pair.2)) _
        rw [PMF.map_comp]
        apply map_congr_on_support _
        intro final member
        simp only [Function.comp_apply, refines final member]
    _ = law.bind fun final => (noise (view (coarse final))).map fun extra =>
          (refine (coarse final), extra) := by
        rw [factored, PMF.bind_bind, PMF.bind_map]
        apply bind_congr_on_support _
        intro final _
        simp only [Function.comp_apply]
        rw [PMF.bind_map]
        rfl
    _ = law.bind fun final => (noise (recover (view (fine final)))).map fun extra =>
          (fine final, extra) := by
        apply bind_congr_on_support _
        intro final member
        rw [recovered final member, refines final member]
    _ = _ := by
        rw [PMF.bind_map]
        rfl

section Split

variable {α β : Type}

/-- The mass of a prior on a set, times the prior restricted to it, is the
prior on that set. -/
private theorem filter_mul_mass (prior : PMF α) (part : Set α)
    (some : ∃ a ∈ part, a ∈ prior.support) (a : α) :
    (∑' other, part.indicator prior other) * prior.filter part some a =
      part.indicator prior a := by
  rw [PMF.filter_apply, mul_comm, mul_assoc,
    ENNReal.inv_mul_cancel ?_ ?_, mul_one]
  · obtain ⟨witness, inside, supported⟩ := some
    intro zero
    have := ENNReal.tsum_eq_zero.mp zero witness
    rw [Set.indicator_of_mem inside] at this
    exact supported this
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (by
      calc (∑' other, part.indicator prior other) ≤ ∑' other, prior other :=
            ENNReal.tsum_le_tsum fun other => Set.indicator_le_self part prior other
        _ = 1 := prior.tsum_coe)

/-- The bind of a prior on a set, through the prior restricted to it. -/
private theorem bind_indicator_eq (prior : PMF α) (part : Set α)
    (some : ∃ a ∈ part, a ∈ prior.support) (continuation : α → PMF β) (b : β) :
    ∑' a, part.indicator prior a * continuation a b =
      (∑' other, part.indicator prior other) *
        ((prior.filter part some).bind continuation) b := by
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  congr 1
  funext a
  rw [← mul_assoc, filter_mul_mass prior part some a]

/-- **Recombining a split prior.** Two continuations with one bind on the
prior restricted to a set and on the prior restricted to its complement have
one bind on the prior. -/
theorem bind_eq_of_split (prior : PMF α) (part : Set α) (first second : α → PMF β)
    (inside : ∀ some : ∃ a ∈ part, a ∈ prior.support,
      (prior.filter part some).bind first = (prior.filter part some).bind second)
    (outside : ∀ some : ∃ a ∈ partᶜ, a ∈ prior.support,
      (prior.filter partᶜ some).bind first = (prior.filter partᶜ some).bind second) :
    prior.bind first = prior.bind second := by
  classical
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  have split (continuation : α → PMF β) :
      ∑' a, prior a * continuation a b =
        ∑' a, part.indicator prior a * continuation a b +
          ∑' a, partᶜ.indicator prior a * continuation a b := by
    rw [← ENNReal.tsum_add]
    congr 1
    funext a
    by_cases member : a ∈ part
    · rw [Set.indicator_of_mem member, Set.indicator_of_notMem (by simpa using member),
        zero_mul, add_zero]
    · rw [Set.indicator_of_notMem member, Set.indicator_of_mem (by simpa using member),
        zero_mul, zero_add]
  have piece (piece : Set α)
      (agree : ∀ some : ∃ a ∈ piece, a ∈ prior.support,
        (prior.filter piece some).bind first = (prior.filter piece some).bind second) :
      ∑' a, piece.indicator prior a * first a b =
        ∑' a, piece.indicator prior a * second a b := by
    by_cases some : ∃ a ∈ piece, a ∈ prior.support
    · rw [bind_indicator_eq prior piece some first b, bind_indicator_eq prior piece some second b,
        agree some]
    · push Not at some
      have vanish (continuation : α → PMF β) :
          ∑' a, piece.indicator prior a * continuation a b = 0 := by
        apply ENNReal.tsum_eq_zero.mpr
        intro a
        by_cases member : a ∈ piece
        · rw [Set.indicator_of_mem member,
            (PMF.apply_eq_zero_iff prior a).mpr (some a member), zero_mul]
        · rw [Set.indicator_of_notMem member, zero_mul]
      rw [vanish first, vanish second]
  rw [split first, split second, piece part inside, piece partᶜ outside]

/-- **Restricting an equality of binds.** When the outputs of two
continuations tell whether their input lies in a set, an equality of their
binds on a prior holds on the prior restricted to that set. -/
theorem bind_filter_eq (prior : PMF α) (part : Set α) (first second : α → PMF β)
    (classify : β → Prop)
    (firstClassified : ∀ a ∈ prior.support, ∀ b ∈ (first a).support, classify b ↔ a ∈ part)
    (secondClassified : ∀ a ∈ prior.support, ∀ b ∈ (second a).support, classify b ↔ a ∈ part)
    (same : prior.bind first = prior.bind second) (some : ∃ a ∈ part, a ∈ prior.support) :
    (prior.filter part some).bind first = (prior.filter part some).bind second := by
  classical
  have mass : (∑' other, part.indicator prior other) ≠ 0 := by
    obtain ⟨witness, inside, supported⟩ := some
    intro zero
    have := ENNReal.tsum_eq_zero.mp zero witness
    rw [Set.indicator_of_mem inside] at this
    exact supported this
  have massFinite : (∑' other, part.indicator prior other) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (by
      calc (∑' other, part.indicator prior other) ≤ ∑' other, prior other :=
            ENNReal.tsum_le_tsum fun other => Set.indicator_le_self part prior other
        _ = 1 := prior.tsum_coe)
  ext b
  have restricted (continuation : α → PMF β)
      (classified : ∀ a ∈ prior.support, ∀ b ∈ (continuation a).support, classify b ↔ a ∈ part) :
      (∑' other, part.indicator prior other) * ((prior.filter part some).bind continuation) b =
        if classify b then (prior.bind continuation) b else 0 := by
    rw [← bind_indicator_eq prior part some continuation b]
    split_ifs with classifiedB
    · rw [PMF.bind_apply]
      congr 1
      funext a
      by_cases member : a ∈ part
      · rw [Set.indicator_of_mem member]
      · rw [Set.indicator_of_notMem member, zero_mul]
        by_cases supported : a ∈ prior.support
        · rw [(PMF.apply_eq_zero_iff (continuation a) b).mpr (fun inSupport =>
            member ((classified a supported b inSupport).mp classifiedB)), mul_zero]
        · rw [(PMF.apply_eq_zero_iff prior a).mpr supported, zero_mul]
    · apply ENNReal.tsum_eq_zero.mpr
      intro a
      by_cases member : a ∈ part
      · rw [Set.indicator_of_mem member]
        by_cases supported : a ∈ prior.support
        · rw [(PMF.apply_eq_zero_iff (continuation a) b).mpr (fun inSupport =>
            classifiedB ((classified a supported b inSupport).mpr member)), mul_zero]
        · rw [(PMF.apply_eq_zero_iff prior a).mpr supported, zero_mul]
      · rw [Set.indicator_of_notMem member, zero_mul]
  have both := (restricted first firstClassified).trans
    ((congrArg (fun law : PMF β => if classify b then law b else 0) same).trans
      (restricted second secondClassified).symm)
  exact (ENNReal.mul_right_inj mass massFinite).mp both

end Split

end Vegas
