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

/-- Agreement on the support of one normalized finite law determines the
other law everywhere. In particular, the other law cannot carry additional
mass outside that support. -/
theorem ext_of_prob_on_support {first second : FinDist α}
    (h : ∀ x ∈ first.support, first.prob x = second.prob x) : first = second := by
  classical
  let onFirstSupport : α → ℝ := fun x => if x ∈ first.support then 1 else 0
  have hexpect : second.expect onFirstSupport = 1 := by
    unfold expect
    rw [tsum_eq_sum (s := first.supportFinset)]
    · simp only [onFirstSupport]
      rw [Finset.sum_congr rfl fun x hx => by
        rw [if_pos (mem_supportFinset.mp hx), ← h x (mem_supportFinset.mp hx)]]
      simpa only [mul_one] using sum_prob_supportFinset first
    · intro x hx
      change second.prob x * (if x ∈ first.support then 1 else 0) = 0
      rw [if_neg (fun hmem => hx (mem_supportFinset.mpr hmem)), mul_zero]
  have hsupport : second.support ⊆ first.support := by
    intro x hx
    have hone := second.eq_of_expect_eq_of_le onFirstSupport 1
      (fun y _ => by simp only [onFirstSupport]; split <;> norm_num) hexpect hx
    by_contra hnot
    simp only [onFirstSupport, if_neg hnot, zero_ne_one] at hone
  apply ext_of_prob
  intro x
  by_cases hx : x ∈ first.support
  · exact h x hx
  · rw [prob_eq_zero_iff.mpr hx, prob_eq_zero_iff.mpr (fun hmem => hx (hsupport hmem))]

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
