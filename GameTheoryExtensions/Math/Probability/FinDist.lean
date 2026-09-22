/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Finite-support composition and branch laws -/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α β : Type*}

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

end GameTheory.Math.Probability.FinDist
