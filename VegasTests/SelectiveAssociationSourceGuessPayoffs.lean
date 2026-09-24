/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceBindingContinuation

/-! # Whole-continuation payoff bounds at source guessing sites -/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

private theorem withheld_guess_payoff_le (a guess : PublicationResult Bool)
    (first own : Bool) :
    correctness (if first then a else .failure) (if own then guess else .failure) -
      openingPenalty (if own then guess else .failure) ≤
        correctness a guess - openingPenalty guess := by
  cases guess with
  | failure => cases own <;> simp
  | success bit =>
      cases own with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, correctness_failure_right,
            openingPenalty_failure, openingPenalty_success, sub_zero]
          have nonneg := correctness_nonneg a (.success bit)
          linarith
      | true =>
          cases first with
          | false => simpa using correctness_nonneg a (.success bit)
          | true => simp

theorem bob_guess_response_payoff_le {Claim : Type}
    (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a c : PublicationResult Bool) (core : execution.application.core = CorePath.carol a c)
    (visited : execution.application.visit = some 2)
    (supported : final ∈ (runInstructions players (afterResponse 2)
      (execution.respond (application Claim) bob response)).support) :
    utility (results final.application) bob ≤
      correctness a (selectedBinding 2 response) - openingPenalty (selectedBinding 2 response) := by
  obtain ⟨first, second, third, result, _, _, _⟩ :=
    bob_binding_response_results players execution final response a c core visited supported
  rw [result, utility_bob]
  exact withheld_guess_payoff_le a (selectedBinding 2 response) first third

theorem carol_guess_response_payoff_le {Claim : Type}
    (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a : PublicationResult Bool) (core : execution.application.core = CorePath.alice a)
    (visited : execution.application.visit = some 1)
    (supported : final ∈ (runInstructions players (afterResponse 1)
      (execution.respond (application Claim) carol response)).support) :
    utility (results final.application) carol ≤
      correctness a (selectedBinding 1 response) - openingPenalty (selectedBinding 1 response) := by
  obtain ⟨b, first, second, third, result, _, _, _⟩ :=
    carol_binding_response_results players execution final response a core visited supported
  rw [result, utility_carol]
  exact withheld_guess_payoff_le a (selectedBinding 1 response) first second

theorem bob_guess_response_payoff_eq {Claim : Type}
    (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a c : PublicationResult Bool) (guess : Bool)
    (core : execution.application.core = CorePath.carol a c)
    (visited : execution.application.visit = some 2)
    (selected : selectedBinding 2 response = .success guess)
    (aliceOpens : OpensAt players 3) (bobOpens : OpensAt players 5)
    (supported : final ∈ (runInstructions players (afterResponse 2)
      (execution.respond (application Claim) bob response)).support) :
    utility (results final.application) bob = correctness a (.success guess) := by
  obtain ⟨first, second, third, result, firstOpens, _, thirdOpens⟩ :=
    bob_binding_response_results players execution final response a c core visited supported
  simp only [result, firstOpens aliceOpens, thirdOpens bobOpens, selected, ↓reduceIte,
    utility_bob, openingPenalty_success, sub_zero]

theorem carol_guess_response_payoff_eq {Claim : Type}
    (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a : PublicationResult Bool) (guess : Bool)
    (core : execution.application.core = CorePath.alice a)
    (visited : execution.application.visit = some 1)
    (selected : selectedBinding 1 response = .success guess)
    (aliceOpens : OpensAt players 3) (carolOpens : OpensAt players 4)
    (supported : final ∈ (runInstructions players (afterResponse 1)
      (execution.respond (application Claim) carol response)).support) :
    utility (results final.application) carol = correctness a (.success guess) := by
  obtain ⟨b, first, second, third, result, firstOpens, secondOpens, _⟩ :=
    carol_binding_response_results players execution final response a core visited supported
  simp only [result, firstOpens aliceOpens, secondOpens carolOpens, selected, ↓reduceIte,
    utility_carol, openingPenalty_success, sub_zero]

theorem finish_bob_guess_payoff_le {Claim : Type}
    (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c : PublicationResult Bool)
    (core : control.execution.application.core = CorePath.carol a c)
    (visited : control.execution.application.visit = some 2)
    (active : control.actor = some bob)
    (remaining : control.remaining = (afterResponse 2).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 2).length + 1) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).expect (fun state => utility (protocolResults state) bob) ≤
        (players bob (control.execution.recall bob)
          (control.execution.observe (application Claim) bob)).expect
            (fun response => correctness a (selectedBinding 2 response) -
              openingPenalty (selectedBinding 2 response)) := by
  rw [finish_response_law players 2 control active remaining position,
    FinDist.expect_map, FinDist.expect_bind]
  apply FinDist.expect_mono
  intro response _
  apply FinDist.expect_le_of_forall
  intro final supported
  exact bob_guess_response_payoff_le players control.execution final response a c core
    visited supported

theorem finish_carol_guess_payoff_le {Claim : Type}
    (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a : PublicationResult Bool)
    (core : control.execution.application.core = CorePath.alice a)
    (visited : control.execution.application.visit = some 1)
    (active : control.actor = some carol)
    (remaining : control.remaining = (afterResponse 1).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 1).length + 1) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).expect (fun state => utility (protocolResults state) carol) ≤
        (players carol (control.execution.recall carol)
          (control.execution.observe (application Claim) carol)).expect
            (fun response => correctness a (selectedBinding 1 response) -
              openingPenalty (selectedBinding 1 response)) := by
  rw [finish_response_law players 1 control active remaining position,
    FinDist.expect_map, FinDist.expect_bind]
  apply FinDist.expect_mono
  intro response _
  apply FinDist.expect_le_of_forall
  intro final supported
  exact carol_guess_response_payoff_le players control.execution final response a core
    visited supported

theorem policy_selected_guess (Claim : Type) (defaultClaim : Claim) (event : Event)
    (guessSite : event = 1 ∨ event = 2) (past : List (application Claim).PlayerEntry)
    (view : (application Claim).PlayerView) (visited : view.application.visit = some event)
    (response : (application Claim).Action)
    (supported : response ∈ (policy Claim defaultClaim (eventOwner event) past view).support) :
    selectedBinding event response = .success (publicGuess view) := by
  have nonzero : event.val ≠ 0 := by rcases guessSite with rfl | rfl <;> decide
  have early : event.val < 3 := by rcases guessSite with rfl | rfl <;> decide
  simp only [policy, visited, ↓reduceIte, nonzero, FinDist.mem_support_pure] at supported
  subst response
  simp [selectedBinding, playing, early]

theorem finish_bob_prescribed_guess (Claim : Type) (defaultClaim : Claim)
    (control : (application Claim).Control) (a c : PublicationResult Bool)
    (core : control.execution.application.core = CorePath.carol a c)
    (visited : control.execution.application.visit = some 2)
    (active : control.actor = some bob)
    (remaining : control.remaining = (afterResponse 2).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 2).length + 1) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
      (policy Claim defaultClaim) (some control)).expect
        (fun state => utility (protocolResults state) bob) =
          correctness a (.success
            (publicGuess (control.execution.observe (application Claim) bob))) := by
  rw [finish_response_law (policy Claim defaultClaim) 2 control active remaining position,
    FinDist.expect_map, FinDist.expect_bind]
  calc
    _ = (policy Claim defaultClaim bob (control.execution.recall bob)
        (control.execution.observe (application Claim) bob)).expect (fun _ =>
          correctness a (.success
            (publicGuess (control.execution.observe (application Claim) bob)))) := by
      apply FinDist.expect_congr
      intro response responseMem
      calc
        _ = (runInstructions (policy Claim defaultClaim) (afterResponse 2)
            (control.execution.respond (application Claim) bob response)).expect (fun _ =>
              correctness a (.success
                (publicGuess (control.execution.observe (application Claim) bob)))) := by
          apply FinDist.expect_congr
          intro final supported
          exact bob_guess_response_payoff_eq _ control.execution final response a c _ core visited
            (policy_selected_guess Claim defaultClaim 2 (Or.inr rfl) _ _ visited _ responseMem)
            (policy_opensAt Claim defaultClaim 3 (by decide))
            (policy_opensAt Claim defaultClaim 5 (by decide)) supported
        _ = _ := FinDist.expect_const ..
    _ = _ := FinDist.expect_const ..

theorem finish_carol_prescribed_guess (Claim : Type) (defaultClaim : Claim)
    (control : (application Claim).Control) (a : PublicationResult Bool)
    (core : control.execution.application.core = CorePath.alice a)
    (visited : control.execution.application.visit = some 1)
    (active : control.actor = some carol)
    (remaining : control.remaining = (afterResponse 1).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 1).length + 1) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
      (policy Claim defaultClaim) (some control)).expect
        (fun state => utility (protocolResults state) carol) =
          correctness a (.success
            (publicGuess (control.execution.observe (application Claim) carol))) := by
  rw [finish_response_law (policy Claim defaultClaim) 1 control active remaining position,
    FinDist.expect_map, FinDist.expect_bind]
  calc
    _ = (policy Claim defaultClaim carol (control.execution.recall carol)
        (control.execution.observe (application Claim) carol)).expect (fun _ =>
          correctness a (.success
            (publicGuess (control.execution.observe (application Claim) carol)))) := by
      apply FinDist.expect_congr
      intro response responseMem
      calc
        _ = (runInstructions (policy Claim defaultClaim) (afterResponse 1)
            (control.execution.respond (application Claim) carol response)).expect (fun _ =>
              correctness a (.success
                (publicGuess (control.execution.observe (application Claim) carol)))) := by
          apply FinDist.expect_congr
          intro final supported
          exact carol_guess_response_payoff_eq _ control.execution final response a _ core visited
            (policy_selected_guess Claim defaultClaim 1 (Or.inl rfl) _ _ visited _ responseMem)
            (policy_opensAt Claim defaultClaim 3 (by decide))
            (policy_opensAt Claim defaultClaim 4 (by decide)) supported
        _ = _ := FinDist.expect_const ..
    _ = _ := FinDist.expect_const ..

end VegasTests.SelectiveAssociation.NamedSource
