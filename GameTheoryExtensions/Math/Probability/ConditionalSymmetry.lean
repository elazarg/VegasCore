/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Support
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Conditional probabilities under an observation-preserving symmetry

An involution preserving a finite law also preserves that law conditioned on
any invariant positive-mass event. Two events exchanged by the involution have
equal conditional probabilities. Other outcomes may remain fixed; in
particular, equality of the two successful bit probabilities does not assume
that failure has probability zero.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {α β : Type*}

theorem apply_involution (law : PMF α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law) (value : α) :
    law (swap value) = law value := by
  conv_lhs => rw [← symmetric]
  exact pmf_map_apply_of_injective law involution.injective value

theorem filter_involution (law : PMF α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law)
    (event : Set α) (invariant : ∀ value, swap value ∈ event ↔ value ∈ event)
    (positive : ∃ value ∈ event, value ∈ law.support) :
    (law.filter event positive).map swap = law.filter event positive := by
  classical
  ext value
  have swapped := pmf_map_apply_of_injective (law.filter event positive)
    involution.injective (swap value)
  rw [involution value] at swapped
  rw [swapped, PMF.filter_apply, PMF.filter_apply]
  congr 1
  by_cases member : value ∈ event
  · have swappedMember := (invariant value).mpr member
    simp only [Set.indicator, member, swappedMember, ↓reduceIte]
    exact apply_involution law swap involution symmetric value
  · have swappedMember : swap value ∉ event := fun inside => member ((invariant value).mp inside)
    simp only [Set.indicator, member, swappedMember, ↓reduceIte]

theorem toOuterMeasure_eq_of_involution (law : PMF α) (swap : α → α)
    (symmetric : law.map swap = law) (first second : Set α)
    (exchanged : ∀ value ∈ law.support, swap value ∈ first ↔ value ∈ second) :
    law.toOuterMeasure first = law.toOuterMeasure second := by
  conv_lhs => rw [← symmetric]
  rw [PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext value
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · exact fun ⟨member, supported⟩ => ⟨(exchanged value supported).mp member, supported⟩
  · exact fun ⟨member, supported⟩ => ⟨(exchanged value supported).mpr member, supported⟩

/-- Equal event probabilities within each observed information fiber. The
symmetry need only exchange the events on the original law's support. -/
theorem filter_observation_toOuterMeasure_eq (law : PMF α) (swap : α → α)
    (involution : Function.Involutive swap) (symmetric : law.map swap = law)
    (observe : α → β) (sameView : ∀ value, observe (swap value) = observe value)
    (info : β) (positive : ∃ value ∈ {value | observe value = info}, value ∈ law.support)
    (first second : Set α)
    (exchanged : ∀ value ∈ law.support, swap value ∈ first ↔ value ∈ second) :
    (law.filter {value | observe value = info} positive).toOuterMeasure first =
      (law.filter {value | observe value = info} positive).toOuterMeasure second := by
  apply toOuterMeasure_eq_of_involution _ swap
    (filter_involution law swap involution symmetric _ (fun value => by
      change observe (swap value) = info ↔ observe value = info
      rw [sameView value]) positive) first second
  intro value supported
  exact exchanged value ((PMF.mem_support_filter_iff _).mp supported).2

end PMF
