/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGame
import GameTheoryExtensions.Analysis.Protocol.InducedInformation

/-! # The payoff gain from selective knowledge of a fair binding

The probability calculation permits failed guesses and later withholding.
It requires an actual independent guess law and successful Alice/Bob results;
the native continuation proof must supply those premises.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas GameTheory.Math.Probability GameTheory.DecisionExperiment

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

theorem fair_guess_reference_value :
    value (FinDist.uniformOfFintype (α := Bool)) (fun _ => ())
      (fun bit guess => correctness (.success bit) guess)
      (fun _ => FinDist.pure (.success false)) = 1 / 2 := by
  rw [value_eq_expect, FinDist.expect_eq_sum]
  simp only [FinDist.expect_pure, FinDist.prob_uniformOfFintype, Fintype.card_bool,
    Nat.cast_ofNat, Fintype.sum_bool, correctness]
  norm_num

/-- A constant correct-or-incorrect report is optimal for the observer with
no signal. Failed reports remain in the observer's action menu. -/
theorem fair_guess_reference_optimal :
    IsBayesOptimal (FinDist.uniformOfFintype (α := Bool)) (fun _ => ())
      (fun bit guess => correctness (.success bit) guess)
      (fun _ => FinDist.pure (.success false)) := by
  intro signal alternative
  cases signal
  have reference := fair_guess_reference_value
  rw [value_eq_expect] at reference
  simpa only [localValue, Set.preimage_const_of_mem, Set.mem_singleton_iff,
    Set.indicator_univ, reference] using fair_guess_le_half alternative

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
  have bound := induced_advantage (FinDist.uniformOfFintype (α := Bool)) (fun _ => ())
    (fun bit guess => correctness (.success bit) guess)
    (fun _ => FinDist.pure (.success false)) (fun _ => guesses)
    fair_guess_reference_optimal outcomes (fun result => utility result alice)
    (fun bit result => correctness (.success bit) result.carol) 1
    (fun bit _ result supported => by
      rw [utility_alice, alice_success bit result supported, bob_correct bit result supported]
      simp)
    (fun bit _ => carol_bound bit)
  rw [fair_guess_reference_value] at bound
  norm_num at bound ⊢
  exact bound

end VegasTests.SelectiveAssociation
