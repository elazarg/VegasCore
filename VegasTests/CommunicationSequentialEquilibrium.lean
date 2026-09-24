/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.CommunicationSequentialNative
import VegasTests.CommunicationSequentialReach

/-! # Sequential equilibria of the actual native disclosure fixture

For either guessing objective, the full bounded native game has a sequential
equilibrium. Alice randomizes over every available packet; Bob optimizes at
every legal information set, including those without authenticated disclosure.
The one common perturbation keeps Alice's policy fixed and gives positive
weight to all of Bob's legal responses. Every Bayes belief remains fixed along
this sequence because Bob has not yet acted at any decision history.

This is equilibrium construction for the existing native game. It is not a
communication-aware source compilation theorem. In particular, the fixture's
passive observation rule is empty; positive partial-leak transfer is separate.
-/

noncomputable section

namespace VegasTests.CommunicationSequentialNative

open Vegas Vegas.EventGraphRuntime Interaction GameTheory
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open SequentialValidation

theorem native_alice_zero (matchBit : Bool) : nativePayoff matchBit false = fun _ => 0 := by
  funext history
  unfold nativePayoff nativeUtility
  cases history.state <;> simp [nativeStateUtility]

/-- This covers every legal native decision information set and every bounded
packet deviation, rather than only the two certified disclosure fibers. -/
theorem native_sequential_equilibrium_exists (matchBit : Bool) :
    ∃ assessment : nativeModel.BehavioralAssessment,
      assessment.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        assessment.continuationContext site (nativePayoff matchBit who) 113) := by
  obtain ⟨assessment, _, equilibrium⟩ :=
    InformationModel.exists_sequential_equilibrium_of_last_decision
      (nativeMenu.uniformAssessment nativeInitialLaw 56 nativeScheduler)
      (nativeMenu.uniform_fullyMixed nativeInitialLaw 56 nativeScheduler)
      nativeAntichain true bob_last_decision
      (nativeMenu.informationSite_allNonterminal nativeInitialLaw 56 nativeScheduler true)
      (decision_reach_invariant _)
      (nativePayoff matchBit)
      (by
        intro who different
        cases who with
        | false => exact native_alice_zero matchBit
        | true => exact (different rfl).elim)
      112
  exact ⟨assessment, equilibrium⟩

/-- The constructed equilibria solve the disclosed guessing problem with
payoff one at either certified view, even if that view is off equilibrium. -/
theorem native_equilibrium_certified_value (matchBit : Bool) :
    ∃ assessment : nativeModel.BehavioralAssessment,
      assessment.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        assessment.continuationContext site (nativePayoff matchBit who) 113) ∧
      ∀ bit : Bool,
        (assessment.continuationContext (nativeBobSite bit) (nativePayoff matchBit true) 113).value
          (assessment.strategy true) = 1 := by
  obtain ⟨assessment, equilibrium⟩ := native_sequential_equilibrium_exists matchBit
  refine ⟨assessment, equilibrium, ?_⟩
  intro bit
  have optimal := equilibrium.1 true (nativeBobSite bit)
    (evidencePolicy (winningAnswer matchBit)) (Set.mem_univ _)
  change (assessment.continuationContext (nativeBobSite bit)
      (nativePayoff matchBit true) 113).value (evidencePolicy (winningAnswer matchBit)) ≤
    (assessment.continuationContext (nativeBobSite bit)
      (nativePayoff matchBit true) 113).value (assessment.strategy true) at optimal
  rw [evidencePolicy_value] at optimal
  apply le_antisymm _ optimal
  rw [native_continuation_value]
  apply FinDist.expect_le_of_forall
  intro guess _
  split <;> norm_num

end VegasTests.CommunicationSequentialNative
