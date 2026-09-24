/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.ContinuationSimulation
import GameTheoryExtensionsTests.IncentiveCone

/-! # Mixing continuation comparisons and its limits

The first example mixes two distinct source continuation sites. Neither source
site alone has the target's prescribed law, but their common-weight mixture
matches both prescribed and deviating laws. Composition retains that mixture.

These are law-level examples, not additional source or target game models. The
last result checks that this sufficient certificate is strictly stronger than
the exact incentive-cone condition.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ContinuationSimulation

open GameTheory GameTheory.Math.Probability

def coin : FinDist Bool := FinDist.uniformOfFintype

def source (_who : Unit) (branch : Bool) : IncentiveComparison (Bool × Bool) :=
  ⟨FinDist.pure (branch, true), FinDist.pure (branch, false)⟩

def middle (_who _comparison : Unit) : IncentiveComparison (Bool × Bool) :=
  ⟨coin.map (fun branch => (branch, true)), coin.map (fun branch => (branch, false))⟩

def target (_who : Unit) (_comparison : Bool) : IncentiveComparison (Bool × Bool) :=
  middle () ()

def first : GameTheory.ContinuationSimulation source middle where
  alternatives _ _ := coin
  prescribed _ _ := rfl
  alternative _ _ := rfl

def second : GameTheory.ContinuationSimulation middle target :=
  .ofMap (fun _ _ => ()) (fun _ _ => rfl) (fun _ _ => rfl)

def composed : GameTheory.ContinuationSimulation source target := first.trans second

theorem composition_retains_mixture (who : Unit) (comparison : Bool) :
    composed.alternatives who comparison = coin := by
  simp only [composed, GameTheory.ContinuationSimulation.trans, second,
    GameTheory.ContinuationSimulation.ofMap, FinDist.pure_bind, first]

/-- A deterministic source-site decoder cannot supply the same certificate. -/
theorem no_single_source_prescribed (branch : Bool) :
    (middle () ()).prescribed ≠ (source () branch).prescribed := by
  intro same
  have projected := congrArg (fun law => law.map Prod.fst) same
  simp only [middle, source, FinDist.map_comp, FinDist.map_pure] at projected
  change coin.map id = FinDist.pure branch at projected
  rw [FinDist.map_id] at projected
  have mass := congrArg (fun law => law.prob (!branch)) projected
  cases branch <;> norm_num [coin, FinDist.prob_uniformOfFintype,
    FinDist.prob_pure_eq_ite] at mass

/-- Matching these law pairs transports every utility satisfying both source
inequalities, including utilities depending on the source-site label. -/
theorem preserves_all_utilities (utility : (Bool × Bool) → Unit → ℝ)
    (respected : ∀ who branch, (source who branch).Holds (utility · who)) :
    ∀ who comparison, (target who comparison).Holds (utility · who) :=
  composed.preserves utility respected

/-- The exact cone criterion can hold even when no law-pair mixture certificate
exists. Failure to find this certificate therefore does not prove impossibility. -/
theorem cone_preservation_without_simulation :
    IncentiveCone.target.difference ∈ IncentiveComparison.cone IncentiveCone.source ∧
      ¬ Nonempty (GameTheory.ContinuationSimulation
        (fun _who : Unit => IncentiveCone.source)
        (fun (_who _comparison : Unit) => IncentiveCone.target)) := by
  refine ⟨IncentiveCone.target_in_cone, ?_⟩
  rintro ⟨simulation⟩
  exact IncentiveCone.no_prescribed_root_mixture (simulation.alternatives () ())
    (simulation.prescribed () ())

def neutral (branch : Bool) : IncentiveComparison Bool :=
  ⟨FinDist.pure branch, FinDist.pure branch⟩

def crossed : IncentiveComparison Bool := ⟨FinDist.pure false, FinDist.pure true⟩

/-- Matching prescribed and deviating laws by unrelated source mixtures is
unsound: every source comparison is an indifference, while the target has a
strictly profitable deviation. Shared weights are essential to the rule. -/
theorem separate_law_matching_insufficient :
    (∃ weights : FinDist Bool,
      crossed.prescribed = weights.bind (fun branch => (neutral branch).prescribed)) ∧
    (∃ weights : FinDist Bool,
      crossed.alternative = weights.bind (fun branch => (neutral branch).alternative)) ∧
    (∀ utility branch, (neutral branch).Holds utility) ∧
    ¬ crossed.Holds (fun outcome => if outcome then 1 else 0) := by
  refine ⟨⟨FinDist.pure false, ?_⟩, ⟨FinDist.pure true, ?_⟩, ?_, ?_⟩
  · simp only [crossed, FinDist.pure_bind, neutral]
  · simp only [crossed, FinDist.pure_bind, neutral]
  · intro utility branch
    exact le_refl _
  · norm_num [crossed, IncentiveComparison.Holds]

end GameTheoryExtensionsTests.ContinuationSimulation
