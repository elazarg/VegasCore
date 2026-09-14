/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Point masses with an identifiable branch -/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α β : Type*}

/-- If an outcome identifies the first draw, its probability is the draw's
mass times the conditional branch mass. The outcome may have probability zero. -/
theorem prob_bind_of_unique_branch (law : FinDist α) (branch : α → FinDist β)
    (outcome : β) (selected : α)
    (hunique : ∀ value ∈ law.support, outcome ∈ (branch value).support → value = selected) :
    (law.bind branch).prob outcome = law.prob selected * (branch selected).prob outcome := by
  classical
  rw [prob_bind, ← expect_ite_eq]
  apply expect_congr
  intro value hvalue
  by_cases heq : selected = value
  · subst value
    simp only [↓reduceIte]
  · rw [if_neg heq, prob_eq_zero_iff]
    exact fun hbranch => heq (hunique value hvalue hbranch).symm

end GameTheory.Math.Probability.FinDist
