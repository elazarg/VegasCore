/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Support

/-! # Support-local algebra of probability mass functions

Pushforwards and binds are determined by their behavior on the support of the
source law. These laws complement the upstream support lemmas.
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {α β γ δ : Type*}

/-- Pushforwards agree when their functions agree everywhere the source law
can actually draw. -/
theorem map_congr_on_support (μ : PMF α) {f g : α → β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.map f = μ.map g := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact bind_congr_on_support μ fun a ha => by rw [Function.comp_apply, h a ha]; rfl

/-- Equal summary laws may be composed with continuations agreeing on every
pair of supported inputs with the same summary. -/
theorem bind_eq_of_map_eq (μ : PMF α) (ν : PMF β)
    (f : α → γ) (g : β → γ) (hmap : μ.map f = ν.map g)
    (F : α → PMF δ) (H : β → PMF δ)
    (hagree : ∀ a ∈ μ.support, ∀ b ∈ ν.support,
      f a = g b → F a = H b) :
    μ.bind F = ν.bind H := by
  classical
  let representative (c : γ) : β :=
    if h : ∃ b ∈ ν.support, g b = c then h.choose else ν.support_nonempty.choose
  let kernel (c : γ) := H (representative c)
  have hrep (c : γ) (hc : c ∈ (ν.map g).support) :
      representative c ∈ ν.support ∧ g (representative c) = c := by
    have hex : ∃ b ∈ ν.support, g b = c := by simpa using hc
    simp only [representative, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hfirst (a : α) (ha : a ∈ μ.support) : F a = kernel (f a) := by
    have hc : f a ∈ (ν.map g).support := by
      rw [← hmap, PMF.support_map]
      exact ⟨a, ha, rfl⟩
    exact hagree a ha _ (hrep _ hc).1 (hrep _ hc).2.symm
  have hsecond (b : β) (hb : b ∈ ν.support) : H b = kernel (g b) := by
    have hc : g b ∈ (μ.map f).support := by
      rw [hmap, PMF.support_map]
      exact ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hab⟩ := (show g b ∈ f '' μ.support by simpa using hc)
    rw [← hagree a ha b hb hab, ← hab]
    exact hfirst a ha
  calc
    μ.bind F = (μ.map f).bind kernel := by
      rw [PMF.bind_map]
      exact bind_congr_on_support μ hfirst
    _ = (ν.map g).bind kernel := congrArg (fun law => law.bind kernel) hmap
    _ = ν.bind H := by
      rw [PMF.bind_map]
      exact bind_congr_on_support ν fun b hb => (hsecond b hb).symm

end GameTheory.Math.Probability
