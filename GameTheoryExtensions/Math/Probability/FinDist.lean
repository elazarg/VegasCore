/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Point masses with an identifiable branch -/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α β : Type*}

/-- Events that agree on a law's support have the same probability. -/
theorem probOf_congr (law : FinDist α) {first second : Set α}
    (hagrees : ∀ outcome ∈ law.support, outcome ∈ first ↔ outcome ∈ second) :
    law.probOf first = law.probOf second := by
  classical
  rw [← expect_indicator_eq_probOf, ← expect_indicator_eq_probOf]
  apply expect_congr
  intro outcome hmem
  simp only [hagrees outcome hmem]

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

/-- A pointwise weighting identity computes an event mass using a normalized
reference law. Neither positive event probability nor division is required. -/
theorem probOf_eq_expect_of_weighting (law reference : FinDist α) (event : Set α)
    [DecidablePred (· ∈ event)]
    (weight : α → ℝ)
    (hweight : ∀ outcome, (if outcome ∈ event then law.prob outcome else 0) =
      weight outcome * reference.prob outcome) :
    law.probOf event = reference.expect weight := by
  classical
  rw [← expect_indicator_eq_probOf, expect, expect]
  apply tsum_congr
  intro outcome
  rw [mul_comm (reference.prob outcome), ← hweight]
  split_ifs <;> simp only [mul_one, mul_zero]

end GameTheory.Math.Probability.FinDist
