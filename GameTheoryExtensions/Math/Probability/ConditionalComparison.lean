/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Bounds
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

variable {α β : Type*}

/-- No finite ambient carrier is required: an injection carrying one event
into another with weakly increasing point masses compares their masses. -/
theorem toOuterMeasure_le_of_injection (law : PMF α) (first second : Set α) (move : α → α)
    (injective : Set.InjOn move (first ∩ law.support))
    (lands : ∀ value ∈ first, value ∈ law.support → move value ∈ second)
    (increases : ∀ value ∈ first, value ∈ law.support → law value ≤ law (move value)) :
    law.toOuterMeasure first ≤ law.toOuterMeasure second := by
  classical
  let source := first ∩ law.support
  have toSecond (value : source) : move value.1 ∈ second :=
    lands value.1 value.2.1 value.2.2
  calc
    law.toOuterMeasure first = law.toOuterMeasure source := by
      rw [← PMF.toOuterMeasure_apply_inter_support]
    _ = ∑' value : source, law value := by
      rw [PMF.toOuterMeasure_apply, ← tsum_subtype]
    _ ≤ ∑' value : source, law (move value) :=
      ENNReal.tsum_le_tsum fun value => increases value.1 value.2.1 value.2.2
    _ ≤ ∑' value : second, law value := by
      let embed : source → second := fun value => ⟨move value.1, toSecond value⟩
      have embedInjective : Function.Injective embed := fun left right same =>
        Subtype.ext (injective left.2 right.2 (congrArg Subtype.val same))
      exact ENNReal.tsum_comp_le_tsum_of_injective embedInjective (fun value => law value)
    _ = law.toOuterMeasure second := by
      rw [PMF.toOuterMeasure_apply, ← tsum_subtype]

/-- Observation-preserving injections compare posterior event probabilities,
including when failure or other outcomes retain positive probability. -/
theorem filter_observation_toOuterMeasure_le (law : PMF α) (first second : Set α)
    (move : α → α) (observe : α → β) (info : β)
    (positive : ∃ value ∈ {value | observe value = info}, value ∈ law.support)
    (injective : Set.InjOn move (first ∩ law.support))
    (lands : ∀ value ∈ first, value ∈ law.support → move value ∈ second)
    (sameView : ∀ value ∈ first, value ∈ law.support → observe (move value) = observe value)
    (increases : ∀ value ∈ first, value ∈ law.support → law value ≤ law (move value)) :
    (law.filter {value | observe value = info} positive).toOuterMeasure first ≤
      (law.filter {value | observe value = info} positive).toOuterMeasure second := by
  classical
  apply toOuterMeasure_le_of_injection _ first second move
  · intro left leftMem right rightMem same
    exact injective ⟨leftMem.1, ((PMF.mem_support_filter_iff _).mp leftMem.2).2⟩
      ⟨rightMem.1, ((PMF.mem_support_filter_iff _).mp rightMem.2).2⟩ same
  · intro value member supported
    exact lands value member ((PMF.mem_support_filter_iff _).mp supported).2
  · intro value member supported
    obtain ⟨observed, supported⟩ := (PMF.mem_support_filter_iff _).mp supported
    have moved : observe (move value) = info :=
      (sameView value member supported).trans observed
    rw [PMF.filter_apply, PMF.filter_apply, Set.indicator_of_mem observed,
      Set.indicator_of_mem (show move value ∈ {value | observe value = info} from moved)]
    exact mul_le_mul_left (increases value member supported) _

/-- A posterior comparison holding throughout a common consistency sequence
holds in its limit. Finiteness is needed to pass from point masses to events. -/
theorem PMFConvergesPointwise.toOuterMeasure_toReal_le
    {α : Type*} [Finite α] {sequence : ℕ → PMF α} {target : PMF α}
    (converges : PMFConvergesPointwise sequence target) (first second : Set α)
    (comparison : ∀ n, ((sequence n).toOuterMeasure first).toReal ≤
      ((sequence n).toOuterMeasure second).toReal) :
    (target.toOuterMeasure first).toReal ≤ (target.toOuterMeasure second).toReal := by
  classical
  let : Fintype α := Fintype.ofFinite α
  have left := converges.expect_finite (fun value => if value ∈ first then (1 : ℝ) else 0)
  have right := converges.expect_finite (fun value => if value ∈ second then (1 : ℝ) else 0)
  simp only [expect_indicator] at left right
  exact le_of_tendsto_of_tendsto left right (Filter.Eventually.of_forall comparison)

end GameTheory.Math.Probability
