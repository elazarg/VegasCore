/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Convergence

/-! # Conditional probability comparisons by history injections

An injection carrying one event into another and weakly increasing point
weights compares their probabilities. If it preserves the observed information,
the comparison holds after conditioning on that information. Unlike a symmetry
argument, this permits a biased law and does not require the map to be surjective.
On finite carriers the inequality survives pointwise limits of belief laws.
-/

noncomputable section

namespace GameTheory.Math.Probability

namespace FinDist

variable {α β : Type*}

open Classical in
theorem probOf_eq_sum_filter (law : FinDist α) (event : Set α) :
    law.probOf event = ∑ value ∈ law.supportFinset.filter (· ∈ event), law.prob value := by
  classical
  rw [← expect_indicator_eq_probOf, expect_eq_sum_support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro value _
  by_cases member : value ∈ event <;> simp [member]

/-- No finite ambient carrier is required: only the law's support is summed. -/
theorem probOf_le_of_injection (law : FinDist α) (first second : Set α) (move : α → α)
    (injective : Set.InjOn move (first ∩ law.support))
    (lands : ∀ value ∈ first, value ∈ law.support → move value ∈ second)
    (increases : ∀ value ∈ first, value ∈ law.support →
      law.prob value ≤ law.prob (move value)) :
    law.probOf first ≤ law.probOf second := by
  classical
  rw [probOf_eq_sum_filter, probOf_eq_sum_filter]
  let source := law.supportFinset.filter (· ∈ first)
  let target := law.supportFinset.filter (· ∈ second)
  have source_mem {value} (member : value ∈ source) :
      value ∈ first ∧ value ∈ law.support := by
    have found := Finset.mem_filter.mp member
    exact ⟨found.2, mem_supportFinset.mp found.1⟩
  have maps : source.image move ⊆ target := by
    intro value member
    obtain ⟨original, sourceMember, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨originalFirst, supported⟩ := source_mem sourceMember
    refine Finset.mem_filter.mpr ⟨mem_supportFinset.mpr ?_,
      lands original originalFirst supported⟩
    exact prob_pos_iff.mp (lt_of_lt_of_le (prob_pos_iff.mpr supported)
      (increases original originalFirst supported))
  calc
    ∑ value ∈ source, law.prob value ≤ ∑ value ∈ source, law.prob (move value) := by
      apply Finset.sum_le_sum
      intro value member
      exact increases value (source_mem member).1 (source_mem member).2
    _ = ∑ value ∈ source.image move, law.prob value := by
      rw [Finset.sum_image]
      intro first firstMem second secondMem same
      exact injective (source_mem firstMem) (source_mem secondMem) same
    _ ≤ ∑ value ∈ target, law.prob value :=
      Finset.sum_le_sum_of_subset_of_nonneg maps (fun value _ _ => law.prob_nonneg value)

/-- Observation-preserving injections compare posterior event probabilities,
including when failure or other outcomes retain positive probability. -/
theorem condOn_observation_probOf_le (law : FinDist α) (first second : Set α)
    (move : α → α) (observe : α → β) (info : β)
    (positive : ∃ value ∈ {value | observe value = info}, value ∈ law.support)
    (injective : Set.InjOn move (first ∩ law.support))
    (lands : ∀ value ∈ first, value ∈ law.support → move value ∈ second)
    (sameView : ∀ value ∈ first, value ∈ law.support → observe (move value) = observe value)
    (increases : ∀ value ∈ first, value ∈ law.support →
      law.prob value ≤ law.prob (move value)) :
    (law.condOn {value | observe value = info} positive).probOf first ≤
      (law.condOn {value | observe value = info} positive).probOf second := by
  classical
  apply probOf_le_of_injection _ first second move
  · intro left leftMem right rightMem same
    exact injective ⟨leftMem.1, (support_condOn _ _ _ leftMem.2).2⟩
      ⟨rightMem.1, (support_condOn _ _ _ rightMem.2).2⟩ same
  · intro value member supported
    exact lands value member (support_condOn _ _ _ supported).2
  · intro value member supported
    obtain ⟨observed, supported⟩ := support_condOn _ _ _ supported
    have moved : observe (move value) = info :=
      (sameView value member supported).trans observed
    rw [prob_condOn, prob_condOn, ite_eq_left observed,
      ite_eq_left (show move value ∈ {value | observe value = info} from moved)]
    exact div_le_div_of_nonneg_right (increases value member supported)
      (le_of_lt (probOf_pos positive))

end FinDist

/-- A posterior comparison holding throughout a common consistency sequence
holds in its limit. Finiteness is needed to pass from point masses to events. -/
theorem FinDistConvergesPointwise.probOf_le
    {α : Type*} [Finite α] {sequence : ℕ → FinDist α} {target : FinDist α}
    (converges : FinDistConvergesPointwise sequence target) (first second : Set α)
    (comparison : ∀ n, (sequence n).probOf first ≤ (sequence n).probOf second) :
    target.probOf first ≤ target.probOf second := by
  classical
  let : Fintype α := Fintype.ofFinite α
  have left := converges.expect (fun value => if value ∈ first then (1 : ℝ) else 0)
  have right := converges.expect (fun value => if value ∈ second then (1 : ℝ) else 0)
  simp only [FinDist.expect_indicator_eq_probOf] at left right
  exact le_of_tendsto_of_tendsto left right (Filter.Eventually.of_forall comparison)

end GameTheory.Math.Probability
