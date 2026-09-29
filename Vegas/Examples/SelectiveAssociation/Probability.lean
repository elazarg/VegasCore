/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.Game
import GameTheoryExtensions.Analysis.Protocol.InducedInformation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # The payoff gain from selective knowledge of a fair binding

The probability calculation permits failed guesses and later withholding.
It requires an actual independent guess law and successful Alice/Bob results;
the native continuation proof must supply those premises.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas GameTheory.Math.Probability GameTheory.DecisionExperiment

theorem correctness_pair (guess : PublicationResult Bool) :
    correctness (.success false) guess + correctness (.success true) guess =
      if guess.isSuccess then 1 else 0 := by
  cases guess with
  | failure => norm_num [correctness, PublicationResult.isSuccess]
  | success value => cases value <;> norm_num [correctness, PublicationResult.isSuccess]

theorem fair_guess_le_half (guesses : PMF (PublicationResult Bool)) :
    expect (PMF.uniformOfFintype Bool)
        (fun bit => expect guesses (correctness (.success bit))) ≤ 1 / 2 := by
  have bound : expect guesses (correctness (.success false)) +
      expect guesses (correctness (.success true)) ≤ 1 := by
    rw [← expect_add_of_finite]
    refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun guess _ => ?_
    rw [correctness_pair]
    split <;> norm_num
  rw [expect_eq_sum]
  simp only [toReal_uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
    Fintype.sum_bool]
  linarith

theorem fair_guess_reference_value :
    value (PMF.uniformOfFintype Bool) (fun _ => ())
      (fun bit guess => correctness (.success bit) guess)
      (fun _ => PMF.pure (.success false)) = 1 / 2 := by
  rw [value_eq_expect _ _ _ _ (payoffIntegrable_of_finite _ _), expect_eq_sum]
  simp only [expect_pure, toReal_uniformOfFintype_apply, Fintype.card_bool,
    Nat.cast_ofNat, Fintype.sum_bool, correctness]
  norm_num

/-- A constant correct-or-incorrect report is optimal for the observer with
no signal. Failed reports remain in the observer's action menu. -/
theorem fair_guess_reference_optimal :
    IsBayesOptimal (PMF.uniformOfFintype Bool) (fun _ => ())
      (fun bit guess => correctness (.success bit) guess)
      (fun _ => PMF.pure (.success false)) := by
  refine ⟨fun _ => ResponseIntegrable.of_finite _ _ _, fun signal alternative _ => ?_⟩
  cases signal
  have reference := fair_guess_reference_value
  rw [value_eq_expect _ _ _ _ (payoffIntegrable_of_finite _ _)] at reference
  simpa only [localValue, Set.preimage_const_of_mem, Set.mem_singleton_iff,
    Set.indicator_univ, reference] using fair_guess_le_half alternative

/-- Operational secrecy for Carol and sequentially forced success for Bob give
Alice a strictly positive gain. This lemma is only the finite expectation
calculation: it does not assume or establish an equilibrium correspondence. -/
theorem selective_advantage (outcomes : Bool → PMF Results)
    (guesses : PMF (PublicationResult Bool))
    (alice_success : ∀ bit result, result ∈ (outcomes bit).support →
      result.alice = .success bit)
    (bob_correct : ∀ bit result, result ∈ (outcomes bit).support →
      result.bob = .success bit)
    (carol_bound : ∀ bit,
      expect (outcomes bit) (fun result => correctness (.success bit) result.carol) ≤
        expect guesses (correctness (.success bit))) :
    1 / 2 ≤ expect ((PMF.uniformOfFintype Bool).bind outcomes)
      (fun result => utility result alice) := by
  have bound := induced_advantage (PMF.uniformOfFintype Bool) (Set.toFinite _) (fun _ => ())
    (fun bit guess => correctness (.success bit) guess)
    (fun _ => PMF.pure (.success false)) (fun _ => guesses)
    fair_guess_reference_optimal (fun _ => ResponseIntegrable.of_finite _ _ _) outcomes
    (fun result => utility result alice)
    (fun bit result => correctness (.success bit) result.carol) 1
    (fun _ _ => ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _⟩)
    (fun bit _ result supported => by
      rw [utility_alice, alice_success bit result supported, bob_correct bit result supported]
      simp)
    (fun bit _ => carol_bound bit)
  rw [fair_guess_reference_value] at bound
  norm_num at bound ⊢
  exact bound

end Vegas.Examples.SelectiveAssociation
