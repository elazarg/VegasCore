/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.InducedInformation
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Partial signals in an induced information advantage

The hidden fact has three equally likely values. The less informed observer
learns whether it is zero, so the observation is neither empty nor complete.
Its optimal reporting probability is two thirds. A player inducing accurate
informed reporting therefore gains at least one third, uniformly over every
randomized policy of the less informed observer.
-/

noncomputable section

namespace GameTheoryExtensionsTests.InducedInformation

open GameTheory.DecisionExperiment GameTheory.Math.Probability

def prior : PMF (Fin 3) := (PMF.uniformOfFintype _)

def observe (state : Fin 3) : Bool := decide (state = 0)

def reference (signal : Bool) : PMF (Fin 3) :=
  PMF.pure (if signal then 0 else 1)

theorem reference_value : value prior observe (reportUtility id) reference = 2 / 3 := by
  rw [value_eq_expect _ _ _ _ (payoffIntegrable_of_finite _ _)]
  norm_num [prior, observe, reference, reportUtility, expect_eq_sum,
    toReal_uniformOfFintype_apply, toReal_pure_apply, Fin.sum_univ_succ]

theorem reference_optimal : IsBayesOptimal prior observe (reportUtility id) reference := by
  refine ⟨fun _ => ResponseIntegrable.of_finite _ _ _, fun signal alternative _ => ?_⟩
  rw [localValue_eq_expect_pure _ (Set.toFinite _) _ _ _ _ (ResponseIntegrable.of_finite _ _ _)]
  refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun action _ => ?_
  cases signal <;> fin_cases action <;>
    norm_num [localValue, prior, observe, reference, reportUtility, expect_eq_sum,
      toReal_uniformOfFintype_apply, toReal_pure_apply, Fin.sum_univ_succ]

/-- Informed score losses reduce the guaranteed margin by precisely the same
amount. At benchmark one this specializes to the one-third information gain. -/
theorem partial_signal_gain (policy : Bool → PMF (Fin 3)) (benchmark : ℝ) :
    benchmark - 2 / 3 ≤
      expect (prior.bind fun state => (policy (observe state)).map fun guess => (state, guess))
        (fun result => benchmark - reportUtility id result.1 result.2) := by
  have bound := induced_advantage prior (Set.toFinite _) observe (reportUtility id) reference
    policy reference_optimal (fun _ => ResponseIntegrable.of_finite _ _ _)
    (fun state => (policy (observe state)).map fun guess => (state, guess))
    (fun result => benchmark - reportUtility id result.1 result.2)
    (fun state result => reportUtility id state result.2) benchmark
    (fun _ _ => ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _⟩)
    (fun state _ result supported => by
      obtain ⟨guess, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact le_rfl)
    (fun state _ => by rw [expect_map]; rfl)
  rwa [reference_value] at bound

example (policy : Bool → PMF (Fin 3)) :
    1 / 3 ≤
      expect (prior.bind fun state => (policy (observe state)).map fun guess => (state, guess))
        (fun result => 1 - reportUtility id result.1 result.2) := by
  have bound := partial_signal_gain policy 1
  norm_num at bound ⊢
  exact bound

/-- The qualitative theorem supplies a margin without choosing any native
reporting policy or imposing optimality on the actual less informed observer. -/
example : ∃ margin : ℝ, 0 < margin ∧
    ∀ (policy : Bool → PMF (Fin 3))
      (outcomes : Fin 3 → PMF (Fin 3 × Fin 3))
      (payoff : Fin 3 × Fin 3 → ℝ) (score : Fin 3 → Fin 3 × Fin 3 → ℝ),
      (∀ state ∈ prior.support, ∀ outcome ∈ (outcomes state).support,
        1 - score state outcome ≤ payoff outcome) →
      (∀ state ∈ prior.support,
        expect (outcomes state) (score state) ≤
          expect (policy (observe state)) (reportUtility id state)) →
      margin ≤ expect (prior.bind outcomes) payoff := by
  obtain ⟨margin, positive, bound⟩ := exists_positive_induced_advantage_of_collision prior
    (Set.toFinite _) observe id (first := 1) (second := 2) (PMF.mem_support_uniformOfFintype _)
      (PMF.mem_support_uniformOfFintype _) (by decide) (by decide)
  exact ⟨margin, positive, fun policy outcomes payoff score payoffBound observationBound =>
    bound policy outcomes payoff score
      (fun _ _ => ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _⟩) payoffBound
      observationBound⟩

/-- Full observation removes this information advantage: the less informed
observer can now report every fact correctly, making the score difference zero. -/
example :
    expect (prior.bind fun state => (PMF.pure state).map fun guess => (state, guess))
      (fun result => 1 - reportUtility id result.1 result.2) = 0 := by
  simp only [PMF.pure_map, expect_bind_of_finite, expect_pure,
    reportUtility, id_eq, ↓reduceIte, sub_self, expect_constant]

end GameTheoryExtensionsTests.InducedInformation
