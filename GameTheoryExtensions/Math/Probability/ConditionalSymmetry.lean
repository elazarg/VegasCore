/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Conditional probabilities under an observation-preserving symmetry

An involution preserving a finite law also preserves that law conditioned on
any invariant positive-mass event. Two events exchanged by the involution have
equal conditional probabilities. Other outcomes may remain fixed; in
particular, equality of the two successful bit probabilities does not assume
that failure has probability zero.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α β : Type*}

theorem prob_involution (law : FinDist α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law) (value : α) :
    law.prob (swap value) = law.prob value := by
  classical
  rw [← symmetric, prob_map_of_injective swap involution.injective]
  rw [symmetric]

theorem condOn_involution (law : FinDist α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law)
    (event : Set α) (invariant : ∀ value, swap value ∈ event ↔ value ∈ event)
    (positive : ∃ value ∈ event, value ∈ law.support) :
    (law.condOn event positive).map swap = law.condOn event positive := by
  classical
  apply ext_of_prob
  intro value
  have swapped := prob_map_of_injective swap involution.injective
    (law.condOn event positive) (swap value)
  rw [involution value] at swapped
  rw [swapped, prob_condOn, prob_condOn, invariant value,
    prob_involution law swap involution symmetric]

theorem probOf_eq_of_involution (law : FinDist α) (swap : α → α)
    (symmetric : law.map swap = law) (first second : Set α)
    (exchanged : ∀ value ∈ law.support, swap value ∈ first ↔ value ∈ second) :
    law.probOf first = law.probOf second := by
  classical
  rw [← expect_indicator_eq_probOf, ← expect_indicator_eq_probOf]
  calc
    law.expect (fun value => if value ∈ first then 1 else 0) =
        (law.map swap).expect (fun value => if value ∈ first then 1 else 0) :=
      congrArg (fun dist => dist.expect (fun value => if value ∈ first then 1 else 0))
        symmetric.symm
    _ = law.expect (fun value => if swap value ∈ first then 1 else 0) := expect_map ..
    _ = _ := expect_congr fun value supported => by rw [exchanged value supported]

/-- Equal event probabilities within each observed information fiber. The
symmetry need only exchange the events on the original law's support. -/
theorem condOn_observation_probOf_eq (law : FinDist α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law)
    (observe : α → β) (sameView : ∀ value, observe (swap value) = observe value)
    (info : β) (positive : ∃ value ∈ {value | observe value = info}, value ∈ law.support)
    (first second : Set α)
    (exchanged : ∀ value ∈ law.support, swap value ∈ first ↔ value ∈ second) :
    (law.condOn {value | observe value = info} positive).probOf first =
      (law.condOn {value | observe value = info} positive).probOf second := by
  apply probOf_eq_of_involution _ swap
    (condOn_involution law swap involution symmetric _ (fun value => by
      change observe (swap value) = info ↔ observe value = info
      rw [sameView value]) positive) first second
  intro value supported
  exact exchanged value ((support_condOn law _ positive supported).2)

end GameTheory.Math.Probability.FinDist
