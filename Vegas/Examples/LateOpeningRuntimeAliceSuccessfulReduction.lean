/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceSuccessfulContinuation
import Vegas.Examples.LateOpeningRuntimeAliceFailureReduction

/-! # Observable receiver choices after accepted sender openings

The receiver's actual typed binding law is shared across private labels and
across unseen first and final openings. Its Safe atom gives the sender's
complete successful payoff table under the original rational raw receiver
policy. No posterior or prescribed choice probabilities are assumed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceSuccessfulReduction

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeAliceSuccessfulContinuation
open LateOpeningRuntimeAliceFailureReduction (bindingLaw)
open LateOpeningRuntimeBobRawBinding (serviced)
open LateOpeningRuntimeBobSuccessDecision (labelGuess)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Equal complete native information determines the same typed result
law even when the original current policy uses private raw aliases. -/
theorem bindingLaw_same_information (players : Player → app.Policy)
    (first second : LateOpeningRuntimeBobSuccessInformation.DecisionHistory weight nonnegative)
    (same : LateOpeningRuntimeBindingObservation.bobInformation first.execution =
      LateOpeningRuntimeBindingObservation.bobInformation second.execution) :
    bindingLaw players first.execution = bindingLaw players second.execution := by
  have recalled : first.execution.recall bob = second.execution.recall bob :=
    congrArg Prod.fst same
  have viewed : first.execution.observe app bob = second.execution.observe app bob :=
    congrArg Prod.snd same
  have results : (fun response : app.Action =>
      (serviced first.execution response).application.config.store (.inr bobBindEvent)) =
      fun response => (serviced second.execution response).application.config.store
        (.inr bobBindEvent) := by
    funext response
    exact LateOpeningRuntimeBobSuccessInformation.response_result_same_information
      weight nonnegative first second recalled viewed response
  unfold bindingLaw
  rw [recalled, viewed, results]

def successfulBindingLaw (players : Player → app.Policy) (bit : Bool) (seen : Bool) :
    PMF (Option (PublicationResult Answer)) :=
  bindingLaw players (answerDecision bit 0 0 seen)

include weight nonnegative in
/-- Neither the private label nor the unseen sending time changes Bob's
current raw policy or its actual typed binding result. -/
theorem successful_binding_law (positive : 0 < weight) (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) :
    bindingLaw players (answerDecision bit label slot seen) =
      successfulBindingLaw players bit seen := by
  apply bindingLaw_same_information weight nonnegative players
    (decisionHistory weight nonnegative positive bit label slot seen samplePossible)
    (decisionHistory weight nonnegative positive bit 0 0 seen (Or.inl rfl))
  change LateOpeningRuntimeBindingObservation.bobInformation
      (answerDecision bit label slot seen) =
    LateOpeningRuntimeBindingObservation.bobInformation (answerDecision bit 0 0 seen)
  fin_cases slot
  · exact answerDecision_first_label_info bit label 0 seen
  · have unseen : seen = false := samplePossible.resolve_left (by decide)
    rw [unseen]
    exact (answerDecision_unseen_timing_info bit 0 label).symm

def safeProbability (players : Player → app.Policy) (bit : Bool) (seen : Bool) : ℝ :=
  ((successfulBindingLaw players bit seen) (some (.success safe))).toReal

theorem safeProbability_mem_Icc (players : Player → app.Policy) (bit : Bool) (seen : Bool) :
    safeProbability players bit seen ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, pmf_toReal_apply_le_one _ _⟩

theorem labelGuess_ne_safe (guessed : Fin 3) : labelGuess guessed ≠ safe := by
  intro same
  have values := congrArg Subtype.val same
  change (guessed.val : Int) + 1 = 0 at values
  omega

theorem successfulValue_safe (reward : ℝ) (label : Fin 3) :
    successfulValue reward label safe = reward / 2 := rfl

theorem successfulValue_labelGuess (reward : ℝ) (label guessed : Fin 3) :
    successfulValue reward label (labelGuess guessed) =
      if label.val < 2 then reward else 0 := by
  have positive : (guessed.val : Int) + 1 ≠ 0 := by omega
  have lower : 1 ≤ (guessed.val : Int) + 1 := by omega
  have upper : (guessed.val : Int) + 1 ≤ 3 := by have := guessed.isLt; omega
  simp [successfulValue, labelGuess, positive, lower, upper]

theorem rational_supported_successful_binding (positive : 0 < weight)
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
    (bit : Bool) (seen : Bool) :
    ∀ result ∈ (successfulBindingLaw players bit seen).support,
      ∃ answer : Answer, result = some (.success answer) ∧
        (answer = safe ∨ ∃ guessed : Fin 3, answer = labelGuess guessed) := by
  intro result supported
  obtain ⟨response, responseSupported, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨answer, bound, permitted, _⟩ := rational_response_payoff weight nonnegative positive
    bit 0 0 seen (Or.inl rfl) reward forfeit deposit forfeitPositive depositPositive
      assessment rational players bobPolicy response responseSupported
  exact ⟨answer, bound, permitted⟩

/-- The successful payoff depends only on the actual probability of Safe;
all three rational label guesses give Alice the same label-dependent reward. -/
theorem successfulBinding_expectation (reward : ℝ) (label : Fin 3)
    (law : PMF (Option (PublicationResult Answer)))
    (supported : ∀ result ∈ law.support,
      ∃ answer : Answer, result = some (.success answer) ∧
        (answer = safe ∨ ∃ guessed : Fin 3, answer = labelGuess guessed)) :
    expect law (successfulBindingValue reward label) =
      if label.val < 2 then reward * (1 - (law (some (.success safe))).toReal / 2)
      else reward * (law (some (.success safe))).toReal / 2 := by
  classical
  let indicator : Option (PublicationResult Answer) → ℝ :=
    fun result => if some (.success safe) = result then 1 else 0
  have indicatorIntegrable : PayoffIntegrable law indicator := payoffIntegrable_ite_one_zero law _
  have indicatorValue : expect law indicator = (law (some (.success safe))).toReal := by
    simpa only [indicator, mul_one] using expect_ite_eq law (some (.success safe)) (1 : ℝ)
  have score : ∀ result ∈ law.support,
      successfulBindingValue reward label result =
        if label.val < 2 then reward - (reward / 2) * indicator result
        else (reward / 2) * indicator result := by
    intro result selected
    obtain ⟨answer, rfl, canonical | ⟨guessed, rfl⟩⟩ := supported result selected
    · rw [canonical]
      simp only [successfulBindingValue, successfulValue_safe, indicator, ite_true]
      split_ifs <;> ring
    · have unequal : some (.success safe) ≠
          (some (.success (labelGuess guessed)) : Option (PublicationResult Answer)) := by
        intro same
        exact (labelGuess_ne_safe guessed).symm
          (PublicationResult.success.inj (Option.some.inj same))
      simp only [successfulBindingValue, successfulValue_labelGuess, indicator,
        ite_eq_right unequal, mul_zero, sub_zero]
  rw [expect_congr_on_support score]
  by_cases low : label.val < 2
  · simp only [low, ite_true]
    rw [expect_sub (payoffIntegrable_constant law reward)
      (payoffIntegrable_const_mul indicatorIntegrable), expect_constant,
        expect_const_mul, indicatorValue]
    ring
  · simp only [low, ite_false]
    rw [expect_const_mul, indicatorValue]
    ring

/-- The closed sender value uses the original raw receiver law, with the
same Safe atom across private labels and unseen first/final send times. -/
theorem receiver_expected_value_closed (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false)
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
    expect (LateOpeningRuntimeSettlementContinuation.receiverCompletion weight nonnegative players
      (answerDecision bit label slot seen))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice) =
      if label.val < 2 then reward * (1 - safeProbability players bit seen / 2)
      else reward * safeProbability players bit seen / 2 := by
  rw [receiver_expected_value weight nonnegative positive bit label slot seen samplePossible
    reward forfeit deposit rewardNonnegative forfeitPositive aliceDepositNonnegative
      bobDepositPositive assessment rational players bobPolicy]
  have mapped : expect (bindingLaw players (answerDecision bit label slot seen))
      (successfulBindingValue reward label) =
      expect (players bob ((answerDecision bit label slot seen).recall bob)
        ((answerDecision bit label slot seen).observe app bob)) (fun response =>
          successfulBindingValue reward label
            ((serviced (answerDecision bit label slot seen) response).application.config.store
              (.inr bobBindEvent))) := expect_map _ _ _
  rw [← mapped, successful_binding_law weight nonnegative positive players bit label slot seen
    samplePossible]
  exact successfulBinding_expectation reward label (successfulBindingLaw players bit seen)
    (rational_supported_successful_binding weight nonnegative positive reward forfeit deposit
      forfeitPositive bobDepositPositive assessment rational players bobPolicy bit seen)

end Vegas.Examples.LateOpeningRuntimeAliceSuccessfulReduction
