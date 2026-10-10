/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyContext
import Vegas.Examples.LateOpeningRuntimeBobBindingTransport
import Vegas.Examples.LateOpeningRuntimeBobDirtyScore
import Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization

/-! # Optimal native receiver bindings after sunk audit charges

The actual raw receiver response law attains the maximum of genuine whole Safe
and label-guess policy values. Every supported response selects a successful
maximizing Safe or label binding throughout the complete information fiber.
The receiver deposit may have either sign because its deduction is already sunk.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobDirtyOptimization

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobDirtyContext LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobBindingTransport LateOpeningRuntimeBobSuccessPayoff
  LateOpeningRuntimeBobBindingDecision

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨14, some bob, execution⟩))
  (ready : execution.application.config.cut.Ready bobBindEvent)
  (current : representative.1.state = some ⟨14, some bob, execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem responseValue_le_scoreValue (dirty : ¬ SilentRecall execution) (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    responseValue weight nonnegative site representative execution trace ready current reward
      forfeit deposit assessment response ≤
        expect (assessment.belief bob site) (fun history =>
          bindingScore (originalLabel (executionOfInformation weight nonnegative site representative
            execution trace ready current history))
              ((servicedBinding execution response).application.config.store (.inr bobBindEvent)) -
                deposit bob) := by
  apply expect_mono _
    (payoffIntegrable_of_bounded _ _ fun history => by
      apply expect_abs_le_of_bounded (show 0 ≤ 1 + |forfeit| + |deposit bob| by positivity)
      intro final
      exact LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final))
    (payoffIntegrable_of_bounded _ _ fun history => by
      have scoreBound := bindingScore_abs_le_one (originalLabel
        (executionOfInformation weight nonnegative site representative execution trace ready
          current history))
        ((servicedBinding execution response).application.config.store (.inr bobBindEvent))
      have difference := abs_sub (bindingScore (originalLabel
        (executionOfInformation weight nonnegative site representative execution trace ready
          current history))
        ((servicedBinding execution response).application.config.store (.inr bobBindEvent)))
        (deposit bob)
      exact difference.trans (add_le_add scoreBound (le_refl |deposit bob|)))
  intro history _
  let recovered := executionOfInformation weight nonnegative site representative execution trace
    ready current history
  have compatible := executionOfInformation_spec weight nonnegative site representative execution
    trace ready current history
  have recoveredTrace := compatible.1 ▸ history.1.trace
  have recoveredReady := ready_same_view _ _ compatible.2.2 ready
  have recoveredDirty : ¬ SilentRecall recovered := by
    intro quiet
    apply dirty
    unfold SilentRecall at quiet ⊢
    rw [compatible.2.1]
    exact quiet
  have recoveredPublished : recovered.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool) := by
    rw [← alice_result_same_view _ _ compatible.2.2]
    exact published
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final))
  intro final reached
  have upper := LateOpeningRuntimeBobDirtyScore.dirty_continuation_payoff_le_score weight
    nonnegative recovered recoveredTrace recoveredReady recoveredDirty bit recoveredPublished
      response _ final reached reward forfeit forfeitNonnegative deposit
  have same := serviced_binding_same_information weight nonnegative execution recovered
    trace recoveredTrace compatible.2.1 compatible.2.2 response
  rwa [← same] at upper

def bestAnswerValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) : ℝ :=
  max ((context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative safe))
    (max ((context weight nonnegative site reward forfeit deposit assessment).value
        (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
          (LateOpeningRuntimeBobSuccessDecision.labelGuess 0)))
      (max ((context weight nonnegative site reward forfeit deposit assessment).value
          (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
            (LateOpeningRuntimeBobSuccessDecision.labelGuess 1)))
        ((context weight nonnegative site reward forfeit deposit assessment).value
          (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
            (LateOpeningRuntimeBobSuccessDecision.labelGuess 2)))))

variable
  (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
  (dirty : ¬ SilentRecall execution) (bit : Bool)
  (published : execution.application.config.store (.inr aliceEvent) =
    some (.success bit : PublicationResult Bool))

include representative execution trace ready current timely dirty bit published in
theorem safe_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative safe) =
        2 / 5 - deposit bob := by
  rw [LateOpeningRuntimeBobDirtyContext.answer_context_value weight nonnegative site
    representative execution trace ready current reward forfeit deposit timely dirty bit published]
  have safeScore (label : Fin 3) : answerScore label safe = 2 / 5 := by
    norm_num [answerScore, safe, answerValue]
  simp only [safeScore, expect_constant]

include representative execution trace ready current timely dirty bit published in
theorem bestAnswerValue_ge_safe
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (2 / 5 : ℝ) - deposit bob ≤
      bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  rw [← safe_context_value weight nonnegative site representative execution trace ready current
    reward forfeit deposit timely dirty bit published assessment]
  exact le_max_left _ _

include representative execution trace ready current timely dirty bit published in
theorem answer_context_value_eq_neg_deposit_of_high
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) (high : 4 ≤ answer.val) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer) =
        -deposit bob := by
  rw [LateOpeningRuntimeBobDirtyContext.answer_context_value weight nonnegative site
    representative execution trace ready current reward forfeit deposit timely dirty bit published]
  calc
    _ = expect _ (fun _ => -deposit bob) := by
      apply expect_congr_on_support
      intro history _
      unfold answerScore
      have labelBound := (originalLabel (executionOfInformation weight nonnegative site
        representative execution trace ready current history)).isLt
      have notSafe : answer.val ≠ 0 := by omega
      have notGuess : answer.val ≠
          ((originalLabel (executionOfInformation weight nonnegative site representative execution
            trace ready current history)).val : Int) + 1 := by omega
      simp only [ite_eq_right notSafe, ite_eq_right notGuess, zero_sub]
    _ = _ := expect_constant _ _

include representative execution trace ready current timely dirty bit published in
theorem answer_value_le_bestAnswerValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer) ≤
        bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  by_cases low : answer.val ≤ 3
  · rcases LateOpeningRuntimeBobSuccessOptimization.answer_safe_or_label_of_low answer low with
      same | ⟨label, same⟩
    · rw [same]
      exact le_max_left _ _
    · rw [same]
      fin_cases label
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · have high : 4 ≤ answer.val := by omega
    rw [answer_context_value_eq_neg_deposit_of_high weight nonnegative site representative execution
      trace ready current reward forfeit deposit timely dirty bit published assessment answer high]
    linarith [bestAnswerValue_ge_safe weight nonnegative site representative execution trace ready
      current reward forfeit deposit timely dirty bit published assessment]

include representative execution trace ready current timely dirty bit published in
theorem response_score_value_le_bestAnswerValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    expect (assessment.belief bob site) (fun history =>
      bindingScore (originalLabel (executionOfInformation weight nonnegative site representative
        execution trace ready current history))
          ((servicedBinding execution response).application.config.store (.inr bobBindEvent)) -
            deposit bob) ≤ bestAnswerValue weight nonnegative site reward forfeit deposit
              assessment := by
  cases selected : (servicedBinding execution response).application.config.store
      (.inr bobBindEvent) with
  | none =>
      simp only [bindingScore, zero_sub, expect_constant]
      linarith [bestAnswerValue_ge_safe weight nonnegative site representative execution trace ready
        current reward forfeit deposit timely dirty bit published assessment]
  | some result =>
      cases result with
      | failure =>
          simp only [bindingScore, zero_sub, expect_constant]
          linarith [bestAnswerValue_ge_safe weight nonnegative site representative execution trace
            ready current reward forfeit deposit timely dirty bit published assessment]
      | success answer =>
          change expect (assessment.belief bob site) (fun history =>
            answerScore (originalLabel (executionOfInformation weight nonnegative site
              representative
              execution trace ready current history)) answer - deposit bob) ≤ _
          rw [← LateOpeningRuntimeBobDirtyContext.answer_context_value weight nonnegative site
            representative execution trace ready current reward forfeit deposit timely dirty bit
              published assessment answer]
          exact answer_value_le_bestAnswerValue weight nonnegative site representative execution
            trace ready current reward forfeit deposit timely dirty bit published assessment answer

theorem responseValue_bounded
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    |responseValue weight nonnegative site representative execution trace ready current reward
      forfeit deposit assessment response| ≤ 1 + |forfeit| + |deposit bob| := by
  apply expect_abs_le_of_bounded (by positivity)
  intro history
  apply expect_abs_le_of_bounded (by positivity)
  intro final
  exact LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
    deposit (app.finished final)

include representative execution trace ready current timely dirty bit published in
theorem responseValue_le_bestAnswerValue (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    responseValue weight nonnegative site representative execution trace ready current reward
      forfeit deposit assessment response ≤
        bestAnswerValue weight nonnegative site reward forfeit deposit assessment :=
  (responseValue_le_scoreValue weight nonnegative site representative execution trace ready current
    reward forfeit deposit dirty bit published forfeitNonnegative assessment response).trans
      (response_score_value_le_bestAnswerValue weight nonnegative site representative execution
        trace ready current reward forfeit deposit timely dirty bit published assessment response)

include representative execution trace ready current timely dirty bit published in
theorem incumbent_value_le_bestAnswerValue (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) ≤
        bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  rw [incumbent_value_eq_response_average weight nonnegative site representative execution trace
    ready current reward forfeit deposit]
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun response => responseValue_bounded weight nonnegative site
      representative execution trace ready current reward forfeit deposit assessment response)
  intro response _
  exact responseValue_le_bestAnswerValue weight nonnegative site representative execution trace
    ready current reward forfeit deposit timely dirty bit published forfeitNonnegative assessment
      response

include representative execution trace ready current timely dirty bit published in
theorem rational_value_eq_bestAnswerValue (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
        bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  apply le_antisymm (incumbent_value_le_bestAnswerValue weight nonnegative site representative
    execution trace ready current reward forfeit deposit timely dirty bit published
      forfeitNonnegative assessment)
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      assessment alternative)).mp rational
  exact max_le
    (comparison (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative safe)
      (Set.mem_univ _))
    (max_le (comparison (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
      (LateOpeningRuntimeBobSuccessDecision.labelGuess 0)) (Set.mem_univ _))
      (max_le (comparison (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
        (LateOpeningRuntimeBobSuccessDecision.labelGuess 1)) (Set.mem_univ _))
        (comparison (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative
          (LateOpeningRuntimeBobSuccessDecision.labelGuess 2)) (Set.mem_univ _))))

include representative execution trace ready current timely dirty bit published in
theorem rational_supported_response_value (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ response ∈ (currentResponses weight nonnegative execution assessment).support,
      responseValue weight nonnegative site representative execution trace ready current reward
        forfeit deposit assessment response =
          bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  apply expect_eq_const_of_le_on_support _ _ _
    (payoffIntegrable_of_bounded _ _ fun response => responseValue_bounded weight nonnegative site
      representative execution trace ready current reward forfeit deposit assessment response)
    (fun response _ => responseValue_le_bestAnswerValue weight nonnegative site representative
      execution trace ready current reward forfeit deposit timely dirty bit published
        forfeitNonnegative assessment response)
  rw [← incumbent_value_eq_response_average weight nonnegative site representative execution
    trace ready current reward forfeit deposit]
  exact rational_value_eq_bestAnswerValue weight nonnegative site representative execution trace
    ready current reward forfeit deposit timely dirty bit published forfeitNonnegative assessment
      rational

include representative execution trace ready current timely dirty bit published in
theorem rational_supported_binding (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ response ∈ (currentResponses weight nonnegative execution assessment).support,
      ∃ answer : Answer,
        (servicedBinding execution response).application.config.store (.inr bobBindEvent) =
          some (.success answer) ∧
        (answer = safe ∨ ∃ label : Fin 3,
          answer = LateOpeningRuntimeBobSuccessDecision.labelGuess label) ∧
        (context weight nonnegative site reward forfeit deposit assessment).value
          (LateOpeningRuntimeEarlyBobSafeMenu.answerFinitePolicy weight nonnegative answer) =
            bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  intro response supported
  have value := rational_supported_response_value weight nonnegative site representative execution
    trace ready current reward forfeit deposit timely dirty bit published forfeitNonnegative
      assessment rational response supported
  have ceiling := responseValue_le_scoreValue weight nonnegative site representative execution
    trace ready current reward forfeit deposit dirty bit published forfeitNonnegative assessment
      response
  rw [value] at ceiling
  have positive := bestAnswerValue_ge_safe weight nonnegative site representative execution trace
    ready current reward forfeit deposit timely dirty bit published assessment
  cases selected : (servicedBinding execution response).application.config.store
      (.inr bobBindEvent) with
  | none =>
      rw [selected] at ceiling
      simp only [bindingScore, zero_sub, expect_constant] at ceiling
      linarith
  | some result =>
      cases result with
      | failure =>
          rw [selected] at ceiling
          simp only [bindingScore, zero_sub, expect_constant] at ceiling
          linarith
      | success answer =>
          rw [selected] at ceiling
          change _ ≤ expect (assessment.belief bob site) (fun history =>
            answerScore (originalLabel (executionOfInformation weight nonnegative site
              representative execution trace ready current history)) answer - deposit bob)
            at ceiling
          rw [← LateOpeningRuntimeBobDirtyContext.answer_context_value weight nonnegative site
            representative execution trace ready current reward forfeit deposit timely dirty bit
              published assessment answer] at ceiling
          have maximizing := le_antisymm
            (answer_value_le_bestAnswerValue weight nonnegative site representative execution trace
              ready current reward forfeit deposit timely dirty bit published assessment answer)
            ceiling
          have low : answer.val ≤ 3 := by
            by_contra contrary
            have high : 4 ≤ answer.val := by omega
            have zero := answer_context_value_eq_neg_deposit_of_high weight nonnegative site
              representative execution trace ready current reward forfeit deposit timely dirty bit
                published assessment answer high
            rw [zero] at maximizing
            linarith
          exact ⟨answer, rfl,
            LateOpeningRuntimeBobSuccessOptimization.answer_safe_or_label_of_low answer low,
              maximizing⟩

end Vegas.Examples.LateOpeningRuntimeBobDirtyOptimization
