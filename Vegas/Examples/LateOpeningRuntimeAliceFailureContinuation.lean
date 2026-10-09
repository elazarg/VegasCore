/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFailurePayoff
import Vegas.Examples.LateOpeningRuntimeBobFailedBindingClean
import Vegas.Examples.LateOpeningRuntimeAliceIncentive

/-! # Sender value under the actual rational receiver policy after omission

Every supported receiver response at a genuine omitted-opening branch binds
a clean logical bit guess, and the original receiver policy publishes it on
every later physical branch. The sender's exact expected value is therefore
read from the original current raw response law. The typed binding result is
used to describe that value and does not constrain the runtime's raw menu.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFailureContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeUtility LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeBindingObservation LateOpeningRuntimeSettlementContinuation
  LateOpeningRuntimeAliceFailurePayoff
open LateOpeningRuntimeBobRawBinding (serviced)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def decisionHistory (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) (samplePossible : slot = 0 ∨ earlySeen = false) :
    LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative where
  execution := failedAnswerDecision bit label slot earlySeen finalSeen
  trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
      (LateOpeningRuntimeBindingObservationWitness.failedAnswerDecision_trace weight nonnegative
        bit label slot earlySeen finalSeen samplePossible).some
  quiet := by
    intro entry member
    rw [failedAnswerDecision_recall] at member
    fin_cases slot
    · change entry ∈ (bobObserved bit label 0 earlySeen).recall bob at member
      rw [bobObserved_first_recall] at member
      cases List.mem_singleton.mp member
      rfl
    · have noSeen : earlySeen = false := samplePossible.resolve_left (by decide)
      rw [noSeen] at member
      change entry ∈ (bobObserved bit label 1 false).recall bob at member
      rw [bobObserved_second_recall] at member
      cases List.mem_singleton.mp member
      rfl
  failed := failedAnswerDecision_publication bit label slot earlySeen finalSeen
  ready := failedAnswerDecision_binding_ready bit label slot earlySeen finalSeen
  timely := by
    rw [failedAnswerDecision_physical]
    change 3 - 3 < 3
    decide

def failureValue (reward : ℝ) (label : Fin 3) (answer : Answer) : ℝ :=
  if (label.val = 0 ∧ answer.val = 5) ∨ (label.val = 1 ∧ answer.val = 4) then reward else 0

def failureBindingValue (reward : ℝ) (label : Fin 3) :
    Option (PublicationResult Answer) → ℝ
  | some (.success answer) => failureValue reward label answer
  | _ => 0

/-- Receiver rationality supplies both a clean bit-guess binding and actual
publication for every later raw branch, with no hidden-history belief premise. -/
theorem rational_response_payoff
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (earlySeen finalSeen : Bool)
    (samplePossible : slot = 0 ∨ earlySeen = false)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (response : app.Action)
    (supported : response ∈ (players bob
      ((failedAnswerDecision bit label slot earlySeen finalSeen).recall bob)
      ((failedAnswerDecision bit label slot earlySeen finalSeen).observe app bob)).support) :
    ∃ answer : Answer,
      (serviced (failedAnswerDecision bit label slot earlySeen finalSeen)
        response).application.config.store (.inr bobBindEvent) = some (.success answer) ∧
      (∃ guessedBit : Bool,
        answer = LateOpeningRuntimeBobBindingDecision.bitGuess guessedBit) ∧
      ∀ final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14
        ((failedAnswerDecision bit label slot earlySeen finalSeen).respond app bob
          response)).support,
        LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
          deposit (app.finished final) alice = failureValue reward label answer -
            forfeit - deposit alice := by
  let decision := decisionHistory weight nonnegative bit label slot earlySeen finalSeen
    samplePossible
  obtain ⟨boundedTrace⟩ := LateOpeningRuntimeBindingObservationWitness.failedAnswerDecision_trace
    weight nonnegative bit label slot earlySeen finalSeen samplePossible
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨14, some bob, decision.execution⟩, boundedTrace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (14 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ := (LateOpeningRuntimeNash.model weight nonnegative)
    |>.exists_informationSite_of_active bob history running rfl
  let representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1 := ⟨history, same.symm⟩
  have current : representative.1.state = some ⟨14, some bob, decision.execution⟩ := rfl
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  have currentSupported : response ∈ (LateOpeningRuntimeBobBindingOptimization.currentResponses
      weight nonnegative decision assessment).support := by
    rw [bobPolicy] at supported
    exact supported
  obtain ⟨material, answer, responseEq, packet, selected, shape, _, _, _, _⟩ :=
    LateOpeningRuntimeBobFailedBindingClean.rational_supported_clean_binding weight nonnegative
      site representative decision current reward forfeit deposit forfeitPositive depositPositive
        assessment localRational response currentSupported
  refine ⟨answer, selected, shape, ?_⟩
  intro final reached
  have available := rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bob (assessment.strategy bob)
      _ _ response currentSupported
  have published : final.application.config.store (.inr bobRevealEvent) = some (.success answer) :=
    by
      have selected' := selected
      have available' := available
      have reached' := reached
      rw [responseEq] at selected' available' reached'
      exact LateOpeningRuntimeBobDisclosurePublication.binding_publication weight nonnegative
        reward forfeit deposit assessment decision.execution boundedTrace decision.quiet
          decision.ready material answer available' selected' packet forfeitPositive depositPositive
            rational players bobPolicy final reached'
  have completeReach : final ∈ (receiverCompletion weight nonnegative players
      (failedAnswerDecision bit label slot earlySeen finalSeen)).support := by
    rw [receiverCompletion, ReactiveApplication.invoke, PMF.bind_map]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨response, supported, reached⟩
  exact failed_completion_payoff weight nonnegative players bit label slot earlySeen finalSeen
    samplePossible final completeReach answer published reward forfeit deposit

theorem failureBindingValue_abs_le (reward : ℝ) (rewardNonnegative : 0 ≤ reward)
    (label : Fin 3) (binding : Option (PublicationResult Answer)) :
    |failureBindingValue reward label binding| ≤ reward := by
  cases binding with
  | none => simpa only [failureBindingValue, abs_zero] using rewardNonnegative
  | some binding =>
      cases binding with
      | failure => simpa only [failureBindingValue, abs_zero] using rewardNonnegative
      | success answer =>
          change |failureValue reward label answer| ≤ reward
          unfold failureValue
          split
          · exact le_of_eq (abs_of_nonneg rewardNonnegative)
          · simpa only [abs_zero] using rewardNonnegative

/-- The original current response law determines the entire omitted-branch
sender value; publication and full audit deductions are exact constants. -/
theorem receiver_expected_value
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (earlySeen finalSeen : Bool)
    (samplePossible : slot = 0 ∨ earlySeen = false)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobDepositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob) :
    expect (receiverCompletion weight nonnegative players
      (failedAnswerDecision bit label slot earlySeen finalSeen))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice) =
    expect (players bob ((failedAnswerDecision bit label slot earlySeen finalSeen).recall bob)
      ((failedAnswerDecision bit label slot earlySeen finalSeen).observe app bob)) (fun response =>
        failureBindingValue reward label
          ((serviced (failedAnswerDecision bit label slot earlySeen finalSeen)
            response).application.config.store (.inr bobBindEvent))) - forfeit - deposit alice := by
  let responses := players bob
    ((failedAnswerDecision bit label slot earlySeen finalSeen).recall bob)
    ((failedAnswerDecision bit label slot earlySeen finalSeen).observe app bob)
  let score : app.Action → ℝ := fun response => failureBindingValue reward label
    ((serviced (failedAnswerDecision bit label slot earlySeen finalSeen)
      response).application.config.store (.inr bobBindEvent))
  have scoreIntegrable : PayoffIntegrable responses score := by
    apply payoffIntegrable_of_bounded responses score (C := reward)
    intro response
    exact failureBindingValue_abs_le reward rewardNonnegative label _
  have value : expect (receiverCompletion weight nonnegative players
      (failedAnswerDecision bit label slot earlySeen finalSeen))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice) =
      expect responses (fun response => score response - forfeit - deposit alice) := by
    have integrable (law : PMF app.Execution) : PayoffIntegrable law
        (fun final => LateOpeningRuntimeNash.payoff reward forfeit
          (fun actual => PMF.pure actual) deposit (app.finished final) alice) :=
      LateOpeningRuntimeAliceContinuation.aliceUtility_integrable rewardNonnegative
        forfeitPositive.le deposit aliceDepositNonnegative law
    unfold receiverCompletion ReactiveApplication.invoke
    rw [PMF.bind_map, expect_bind_tower _ _ _ (integrable _)]
    apply expect_congr_on_support
    intro response supported
    obtain ⟨answer, selected, _, exactValue⟩ := rational_response_payoff weight nonnegative
      bit label slot earlySeen finalSeen samplePossible reward forfeit deposit forfeitPositive
        bobDepositPositive assessment rational players bobPolicy response supported
    change _ = failureBindingValue reward label
      ((serviced (failedAnswerDecision bit label slot earlySeen finalSeen)
        response).application.config.store (.inr bobBindEvent)) - forfeit - deposit alice
    rw [selected]
    change _ = failureValue reward label answer - forfeit - deposit alice
    calc
      _ = expect _ (fun _ => failureValue reward label answer - forfeit - deposit alice) :=
        expect_congr_on_support exactValue
      _ = _ := expect_constant _ _
  rw [value, expect_sub (payoffIntegrable_sub scoreIntegrable
    (payoffIntegrable_constant responses forfeit))
      (payoffIntegrable_constant responses (deposit alice)),
    expect_sub scoreIntegrable (payoffIntegrable_constant responses forfeit),
    expect_constant, expect_constant]

end Vegas.Examples.LateOpeningRuntimeAliceFailureContinuation
