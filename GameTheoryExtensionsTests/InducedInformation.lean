/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.InducedInformation

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

def prior : FinDist (Fin 3) := FinDist.uniformOfFintype

def observe (state : Fin 3) : Bool := decide (state = 0)

def reference (signal : Bool) : FinDist (Fin 3) :=
  FinDist.pure (if signal then 0 else 1)

theorem reference_value : value prior observe (reportUtility id) reference = 2 / 3 := by
  rw [value_eq_expect]
  norm_num [prior, observe, reference, reportUtility, FinDist.expect_eq_sum,
    FinDist.prob_uniformOfFintype, FinDist.prob_pure_eq_ite, Fin.sum_univ_succ]

theorem reference_optimal : IsBayesOptimal prior observe (reportUtility id) reference := by
  intro signal alternative
  rw [localValue_eq_expect_pure]
  apply FinDist.expect_le_of_forall
  intro action _
  cases signal <;> fin_cases action <;>
    norm_num [localValue, prior, observe, reference, reportUtility, FinDist.expect_eq_sum,
      FinDist.prob_uniformOfFintype, FinDist.prob_pure_eq_ite, Fin.sum_univ_succ]

/-- Informed score losses reduce the guaranteed margin by precisely the same
amount. At benchmark one this specializes to the one-third information gain. -/
theorem partial_signal_gain (policy : Bool → FinDist (Fin 3)) (benchmark : ℝ) :
    benchmark - 2 / 3 ≤
      (prior.bind fun state => (policy (observe state)).map fun guess => (state, guess)).expect
        (fun result => benchmark - reportUtility id result.1 result.2) := by
  have bound := induced_advantage prior observe (reportUtility id) reference policy
    reference_optimal
    (fun state => (policy (observe state)).map fun guess => (state, guess))
    (fun result => benchmark - reportUtility id result.1 result.2)
    (fun state result => reportUtility id state result.2) benchmark
    (fun state _ result supported => by
      obtain ⟨guess, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact le_rfl)
    (fun state _ => by rw [FinDist.expect_map])
  rwa [reference_value] at bound

example (policy : Bool → FinDist (Fin 3)) :
    1 / 3 ≤
      (prior.bind fun state => (policy (observe state)).map fun guess => (state, guess)).expect
        (fun result => 1 - reportUtility id result.1 result.2) := by
  have bound := partial_signal_gain policy 1
  norm_num at bound ⊢
  exact bound

/-- The qualitative theorem supplies a margin without choosing any native
reporting policy or imposing optimality on the actual less informed observer. -/
example : ∃ margin : ℝ, 0 < margin ∧
    ∀ (policy : Bool → FinDist (Fin 3))
      (outcomes : Fin 3 → FinDist (Fin 3 × Fin 3))
      (payoff : Fin 3 × Fin 3 → ℝ) (score : Fin 3 → Fin 3 × Fin 3 → ℝ),
      (∀ state ∈ prior.support, ∀ outcome ∈ (outcomes state).support,
        1 - score state outcome ≤ payoff outcome) →
      (∀ state ∈ prior.support,
        (outcomes state).expect (score state) ≤
          (policy (observe state)).expect (reportUtility id state)) →
      margin ≤ (prior.bind outcomes).expect payoff := by
  exact exists_positive_induced_advantage_of_collision prior observe id
    (first := 1) (second := 2) (FinDist.mem_support_uniformOfFintype _)
      (FinDist.mem_support_uniformOfFintype _) (by decide) (by decide)

/-- Full observation removes this information advantage: the less informed
observer can now report every fact correctly, making the score difference zero. -/
example :
    (prior.bind fun state => (FinDist.pure state).map fun guess => (state, guess)).expect
      (fun result => 1 - reportUtility id result.1 result.2) = 0 := by
  simp only [FinDist.map_pure, FinDist.expect_bind, FinDist.expect_pure,
    reportUtility, id_eq, ↓reduceIte, sub_self, FinDist.expect_const]

end GameTheoryExtensionsTests.InducedInformation
