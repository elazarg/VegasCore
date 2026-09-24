/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGame

/-! # The payoff gain from selective knowledge of a fair binding

The probability calculation permits failed guesses and later withholding.
It requires an actual independent guess law and successful Alice/Bob results;
the native continuation proof must supply those premises.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas GameTheory.Math.Probability

theorem correctness_pair (guess : PublicationResult Bool) :
    correctness (.success false) guess + correctness (.success true) guess =
      if guess.isSuccess then 1 else 0 := by
  cases guess with
  | failure => norm_num [correctness, PublicationResult.isSuccess]
  | success value => cases value <;> norm_num [correctness, PublicationResult.isSuccess]

theorem fair_guess_le_half (guesses : FinDist (PublicationResult Bool)) :
    (FinDist.uniformOfFintype (α := Bool)).expect
        (fun bit => guesses.expect (correctness (.success bit))) ≤ 1 / 2 := by
  have bound : guesses.expect (correctness (.success false)) +
      guesses.expect (correctness (.success true)) ≤ 1 := by
    rw [← FinDist.expect_add]
    apply FinDist.expect_le_of_forall
    intro guess _
    rw [correctness_pair]
    split <;> norm_num
  rw [FinDist.expect_eq_sum]
  simp only [FinDist.prob_uniformOfFintype, Fintype.card_bool, Nat.cast_ofNat,
    Fintype.sum_bool]
  linarith

/-- A later publication cannot improve on a guess already fixed independently
of the fair hidden bit if it only publishes that guess or withholds it. -/
theorem fair_disclosure_le_half (outcomes : Bool → FinDist Results)
    (guesses : FinDist (PublicationResult Bool))
    (bounded : ∀ bit,
      (outcomes bit).expect (fun result => correctness (.success bit) result.carol) ≤
        guesses.expect (correctness (.success bit))) :
    (FinDist.uniformOfFintype (α := Bool)).expect (fun bit =>
      (outcomes bit).expect (fun result => correctness (.success bit) result.carol)) ≤ 1 / 2 := by
  apply le_trans _ (fair_guess_le_half guesses)
  exact FinDist.expect_mono (fun bit _ => bounded bit)

/-- Operational secrecy for Carol and sequentially forced success for Bob give
Alice a strictly positive gain. This lemma is only the finite expectation
calculation: it does not assume or establish an equilibrium correspondence. -/
theorem selective_advantage (outcomes : Bool → FinDist Results)
    (guesses : FinDist (PublicationResult Bool))
    (alice_success : ∀ bit result, result ∈ (outcomes bit).support →
      result.alice = .success bit)
    (bob_correct : ∀ bit result, result ∈ (outcomes bit).support →
      result.bob = .success bit)
    (carol_bound : ∀ bit,
      (outcomes bit).expect (fun result => correctness (.success bit) result.carol) ≤
        guesses.expect (correctness (.success bit))) :
    1 / 2 ≤ ((FinDist.uniformOfFintype (α := Bool)).bind outcomes).expect
      (fun result => utility result alice) := by
  have value (bit : Bool) : (outcomes bit).expect (fun result => utility result alice) =
      1 - (outcomes bit).expect (fun result => correctness (.success bit) result.carol) := by
    rw [← FinDist.expect_const (outcomes bit) 1, ← FinDist.expect_sub]
    apply FinDist.expect_congr
    intro result member
    rw [utility_alice, alice_success bit result member, bob_correct bit result member]
    simp
  rw [FinDist.expect_bind]
  simp_rw [value]
  rw [FinDist.expect_sub, FinDist.expect_const]
  have bound := fair_disclosure_le_half outcomes guesses carol_bound
  linarith

end VegasTests.SelectiveAssociation
