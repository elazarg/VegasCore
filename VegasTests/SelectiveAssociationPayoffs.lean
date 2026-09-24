/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGame

/-! # Payoff bounds for ordinary opening incentives

The failure penalty is four. A successful Alice opening gives at least minus
one regardless of either guesser's subsequent disclosure; her failure gives
minus four. A successful guesser opening gives at least zero regardless of
Alice's result, while that guesser's failure gives minus four. These bounds
permit strict continuation comparisons without fixing the other disclosures.
They establish payoff inequalities, not availability of opening actions.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas

theorem correctness_nonneg (value guess : PublicationResult Bool) :
    0 ≤ correctness value guess := by
  cases value <;> cases guess <;> simp only [correctness]
  all_goals try split
  all_goals norm_num

theorem correctness_le_one (value guess : PublicationResult Bool) :
    correctness value guess ≤ 1 := by
  cases value <;> cases guess <;> simp only [correctness]
  all_goals try split
  all_goals norm_num

@[simp] theorem utility_alice_failure (bobResult carolResult : PublicationResult Bool) :
    utility ⟨.failure, bobResult, carolResult⟩ alice = -4 := by simp [utility_alice]

@[simp] theorem utility_bob_failure (aliceResult carolResult : PublicationResult Bool) :
    utility ⟨aliceResult, .failure, carolResult⟩ bob = -4 := by simp [utility_bob]

@[simp] theorem utility_carol_failure (aliceResult bobResult : PublicationResult Bool) :
    utility ⟨aliceResult, bobResult, .failure⟩ carol = -4 := by simp [utility_carol]

theorem utility_alice_success_bounds (bit : Bool)
    (bobResult carolResult : PublicationResult Bool) :
    -1 ≤ utility ⟨.success bit, bobResult, carolResult⟩ alice ∧
      utility ⟨.success bit, bobResult, carolResult⟩ alice ≤ 1 := by
  simp only [utility_alice, openingPenalty_success, sub_zero]
  have bobNonneg := correctness_nonneg (.success bit) bobResult
  have bobBound := correctness_le_one (.success bit) bobResult
  have carolNonneg := correctness_nonneg (.success bit) carolResult
  have carolBound := correctness_le_one (.success bit) carolResult
  constructor <;> linarith

theorem utility_bob_success_bounds (bit : Bool)
    (aliceResult carolResult : PublicationResult Bool) :
    0 ≤ utility ⟨aliceResult, .success bit, carolResult⟩ bob ∧
      utility ⟨aliceResult, .success bit, carolResult⟩ bob ≤ 1 := by
  simp only [utility_bob, openingPenalty_success, sub_zero]
  exact ⟨correctness_nonneg _ _, correctness_le_one _ _⟩

theorem utility_carol_success_bounds (bit : Bool)
    (aliceResult bobResult : PublicationResult Bool) :
    0 ≤ utility ⟨aliceResult, bobResult, .success bit⟩ carol ∧
      utility ⟨aliceResult, bobResult, .success bit⟩ carol ≤ 1 := by
  simp only [utility_carol, openingPenalty_success, sub_zero]
  exact ⟨correctness_nonneg _ _, correctness_le_one _ _⟩

/-- Other players' results may differ between the two continuations. -/
theorem utility_alice_opening_gap (bit : Bool)
    (failedBob failedCarol openedBob openedCarol : PublicationResult Bool) :
    utility ⟨.failure, failedBob, failedCarol⟩ alice + 3 ≤
      utility ⟨.success bit, openedBob, openedCarol⟩ alice := by
  rw [utility_alice_failure]
  have bound := (utility_alice_success_bounds bit openedBob openedCarol).1
  linarith

theorem utility_bob_opening_gap (bit : Bool)
    (failedAlice failedCarol openedAlice openedCarol : PublicationResult Bool) :
    utility ⟨failedAlice, .failure, failedCarol⟩ bob + 4 ≤
      utility ⟨openedAlice, .success bit, openedCarol⟩ bob := by
  rw [utility_bob_failure]
  have bound := (utility_bob_success_bounds bit openedAlice openedCarol).1
  linarith

theorem utility_carol_opening_gap (bit : Bool)
    (failedAlice failedBob openedAlice openedBob : PublicationResult Bool) :
    utility ⟨failedAlice, failedBob, .failure⟩ carol + 4 ≤
      utility ⟨openedAlice, openedBob, .success bit⟩ carol := by
  rw [utility_carol_failure]
  have bound := (utility_carol_success_bounds bit openedAlice openedBob).1
  linarith

theorem utility_alice_bounds (result : Results) :
    -4 ≤ utility result alice ∧ utility result alice ≤ 1 := by
  rcases result with ⟨aliceResult, bobResult, carolResult⟩
  cases aliceResult with
  | failure => norm_num
  | success bit =>
      obtain ⟨lower, upper⟩ := utility_alice_success_bounds bit bobResult carolResult
      exact ⟨by linarith, upper⟩

theorem utility_bob_bounds (result : Results) :
    -4 ≤ utility result bob ∧ utility result bob ≤ 1 := by
  rcases result with ⟨aliceResult, bobResult, carolResult⟩
  cases bobResult with
  | failure => norm_num
  | success bit =>
      obtain ⟨lower, upper⟩ := utility_bob_success_bounds bit aliceResult carolResult
      exact ⟨by linarith, upper⟩

theorem utility_carol_bounds (result : Results) :
    -4 ≤ utility result carol ∧ utility result carol ≤ 1 := by
  rcases result with ⟨aliceResult, bobResult, carolResult⟩
  cases carolResult with
  | failure => norm_num
  | success bit =>
      obtain ⟨lower, upper⟩ := utility_carol_success_bounds bit aliceResult bobResult
      exact ⟨by linarith, upper⟩

theorem utility_bob_eq_one_iff (result : Results) :
    utility result bob = 1 ↔
      ∃ bit, result.alice = .success bit ∧ result.bob = .success bit := by
  rcases result with ⟨aliceResult, bobResult, carolResult⟩
  cases aliceResult <;> cases bobResult <;> simp [utility_bob, correctness, eq_comm] <;> norm_num

theorem utility_carol_eq_one_iff (result : Results) :
    utility result carol = 1 ↔
      ∃ bit, result.alice = .success bit ∧ result.carol = .success bit := by
  rcases result with ⟨aliceResult, bobResult, carolResult⟩
  cases aliceResult <;> cases carolResult <;>
    simp [utility_carol, correctness, eq_comm] <;> norm_num

end VegasTests.SelectiveAssociation
