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

/-- A support-dependent continuation after a pushforward can instead be
evaluated at each original draw. The pushforward need not be injective. -/
theorem bindOnSupport_map {γ : Type*} (law : FinDist α) (f : α → β)
    (next : ∀ value ∈ (law.map f).support, FinDist γ) :
    (law.map f).bindOnSupport next = law.bindOnSupport fun value supported =>
      next (f value) (by rw [support_map]; exact ⟨value, supported, rfl⟩) := by
  classical
  obtain ⟨someValue, someSupported⟩ := (law.map f).support_nonempty
  let total : β → FinDist γ := fun value =>
    if supported : value ∈ (law.map f).support then next value supported
    else next someValue someSupported
  have agrees : ∀ value (supported : value ∈ (law.map f).support),
      next value supported = total value := by
    intro value supported
    dsimp only [total]
    rw [dif_pos supported]
  rw [bindOnSupport_eq_bind_of_eq_on_support agrees, bind_map]
  symm
  apply bindOnSupport_eq_bind_of_eq_on_support
  intro value supported
  exact agrees (f value) (by rw [support_map]; exact ⟨value, supported, rfl⟩)

/-- Support-dependent composition is associative.  The evidence for the final
continuation is constructed from the two realized support witnesses, so no
arbitrary off-support continuation is needed. -/
@[simp]
theorem bindOnSupport_bindOnSupport {γ : Type*} (law : FinDist α)
    (first : ∀ value ∈ law.support, FinDist β)
    (next : ∀ value ∈ (law.bindOnSupport first).support, FinDist γ) :
    (law.bindOnSupport first).bindOnSupport next =
      law.bindOnSupport fun value valueMem =>
        (first value valueMem).bindOnSupport fun result resultMem =>
          next result (by
            rw [support_bindOnSupport]
            exact Set.mem_iUnion_of_mem value
              (Set.mem_iUnion_of_mem valueMem resultMem)) := by
  apply ext
  change
    ((law.toPMF.bindOnSupport fun value valueMem =>
      (first value valueMem).toPMF).bindOnSupport fun value valueMem =>
        (next value valueMem).toPMF) = _
  exact PMF.bindOnSupport_bindOnSupport law.toPMF
    (fun value valueMem => (first value valueMem).toPMF)
    (fun value valueMem => (next value valueMem).toPMF)

/-- Associativity when the first continuation is total but the final one uses
support evidence. -/
theorem bind_bindOnSupport_assoc {γ : Type*} (law : FinDist α)
    (first : α → FinDist β)
    (next : ∀ value ∈ (law.bind first).support, FinDist γ) :
    (law.bind first).bindOnSupport next =
      law.bindOnSupport fun value valueMem =>
        (first value).bindOnSupport fun result resultMem =>
          next result (by
            rw [support_bind]
            exact Set.mem_iUnion_of_mem value
              (Set.mem_iUnion_of_mem valueMem resultMem)) := by
  let dependentFirst : ∀ value ∈ law.support, FinDist β := fun value _ => first value
  have sourceEq : law.bindOnSupport dependentFirst = law.bind first :=
    bindOnSupport_eq_bind law first
  calc
    (law.bind first).bindOnSupport next =
        (law.bindOnSupport dependentFirst).bindOnSupport
          (fun value valueMem => next value (by rwa [sourceEq] at valueMem)) := by
      apply bindOnSupport_congr_measure sourceEq.symm
      intro value _ _
      congr
    _ = law.bindOnSupport fun value valueMem =>
          (first value).bindOnSupport fun result resultMem =>
            next result (by
              rw [support_bind]
              exact Set.mem_iUnion_of_mem value
                (Set.mem_iUnion_of_mem valueMem resultMem)) := by
      exact bindOnSupport_bindOnSupport law dependentFirst _

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
