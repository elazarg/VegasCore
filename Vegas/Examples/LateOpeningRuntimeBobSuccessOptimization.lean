/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSuccessDecision

/-! # Optimal first bindings after successful Alice publication

All raw current responses select one typed binding throughout the full native
information class. Under arbitrary actual beliefs their score is bounded by
Safe or the best private-label guess. Genuine whole answer policies attain
that bound, so rational responses bind only maximizing Safe or label answers.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobSuccessInformation
  LateOpeningRuntimeBobSuccessDecision LateOpeningRuntimeBobSuccessPayoff
  LateOpeningRuntimeEarlyBobSafeMenu
open LateOpeningRuntimeBobRawBinding (serviced)
open LateOpeningRuntimeBobBindingDecision (context context_integrable)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

def bestAnswerValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) : ℝ :=
  max ((context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative safe))
    (max ((context weight nonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight nonnegative (labelGuess 0)))
      (max ((context weight nonnegative site reward forfeit deposit assessment).value
          (answerFinitePolicy weight nonnegative (labelGuess 1)))
        ((context weight nonnegative site reward forfeit deposit assessment).value
          (answerFinitePolicy weight nonnegative (labelGuess 2)))))

theorem bestAnswerValue_formula
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    bestAnswerValue weight nonnegative site reward forfeit deposit assessment =
      max (2 / 5) (max (labelMass weight nonnegative site representative decision current
        assessment 0) (max (labelMass weight nonnegative site representative decision current
          assessment 1) (labelMass weight nonnegative site representative decision current
            assessment 2))) := by
  unfold bestAnswerValue
  rw [safe_context_value weight nonnegative site representative decision current,
    label_guess_context_value weight nonnegative site representative decision current,
    label_guess_context_value weight nonnegative site representative decision current,
    label_guess_context_value weight nonnegative site representative decision current]

include representative decision current in
theorem bestAnswerValue_ge_safe
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (2 / 5 : ℝ) ≤ bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  rw [← safe_context_value weight nonnegative site representative decision current reward forfeit
    deposit assessment]
  exact le_max_left _ _

theorem answer_safe_or_label_of_low (answer : Answer) (low : answer.val ≤ 3) :
    answer = safe ∨ ∃ label : Fin 3, answer = labelGuess label := by
  by_cases zero : answer.val = 0
  · exact Or.inl (Subtype.ext zero)
  · have bounded : 0 ≤ answer.val ∧ answer.val ≤ 5 := answer.property
    let label : Fin 3 := ⟨(answer.val - 1).toNat, by omega⟩
    refine Or.inr ⟨label, ?_⟩
    apply Subtype.ext
    dsimp only [labelGuess, label]
    omega

include representative decision current in
theorem answer_value_le_bestAnswerValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) ≤
        bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  by_cases low : answer.val ≤ 3
  · rcases answer_safe_or_label_of_low answer low with same | ⟨label, same⟩
    · rw [same]
      exact le_max_left _ _
    · rw [same]
      fin_cases label
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · have high : 4 ≤ answer.val := by omega
    rw [answer_context_value_eq_zero_of_high weight nonnegative site representative decision current
      reward forfeit deposit assessment answer high]
    linarith [bestAnswerValue_ge_safe weight nonnegative site representative decision current
      reward forfeit deposit assessment]

include representative decision current in
/-- The expected ceiling of any fixed raw response is bounded by the four
actual clean Safe and label-guess values at this information class. -/
theorem response_score_value_le_bestAnswerValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    expect (assessment.belief bob site) (fun history =>
      bindingScore (originalLabel (decisionOfInformation weight nonnegative site representative
        decision current history).execution)
          ((serviced decision.execution response).application.config.store (.inr bobBindEvent))) ≤
      bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  cases selected : (serviced decision.execution response).application.config.store
      (.inr bobBindEvent) with
  | none =>
      simp only [bindingScore, expect_constant]
      linarith [bestAnswerValue_ge_safe weight nonnegative site representative decision current
        reward forfeit deposit assessment]
  | some result =>
      cases result with
      | failure =>
          simp only [bindingScore, expect_constant]
          linarith [bestAnswerValue_ge_safe weight nonnegative site representative decision current
            reward forfeit deposit assessment]
      | success answer =>
          change expect (assessment.belief bob site) (fun history =>
            answerScore (originalLabel (decisionOfInformation weight nonnegative site
              representative decision current history).execution) answer) ≤ _
          rw [← answer_context_value weight nonnegative site representative decision current
            reward forfeit deposit assessment answer]
          exact answer_value_le_bestAnswerValue weight nonnegative site representative decision
            current reward forfeit deposit assessment answer

def currentResponses
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Action :=
  rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
      (decision.execution.recall bob) (decision.execution.observe app bob)

def responseValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) : ℝ :=
  expect (assessment.belief bob site) fun history =>
    expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) 14
      ((decisionOfInformation weight nonnegative site representative decision current
        history).execution.respond app bob response)) fun final =>
          LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
            deposit (app.finished final) bob

theorem responseValue_bounded
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    |responseValue weight nonnegative site representative decision current reward forfeit deposit
      assessment response| ≤ 1 + |forfeit| + |deposit bob| := by
  apply expect_abs_le_of_bounded (by positivity)
  intro history
  apply expect_abs_le_of_bounded (by positivity)
  intro final
  exact LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
    deposit (app.finished final)

theorem responseValue_le_scoreValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    responseValue weight nonnegative site representative decision current reward forfeit deposit
      assessment response ≤ expect (assessment.belief bob site) (fun history =>
        bindingScore (originalLabel (decisionOfInformation weight nonnegative site representative
          decision current history).execution)
            ((serviced decision.execution response).application.config.store
              (.inr bobBindEvent))) := by
  apply expect_mono _
    (payoffIntegrable_of_bounded _ _ fun history => by
      apply expect_abs_le_of_bounded (show 0 ≤ 1 + |forfeit| + |deposit bob| by positivity)
      intro final
      exact LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final))
    (payoffIntegrable_of_bounded _ _ fun history => bindingScore_abs_le_one _ _)
  intro history _
  let recovered := decisionOfInformation weight nonnegative site representative decision current
    history
  have compatible := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final))
  intro final reached
  have upper := continuation_payoff_le_score weight nonnegative recovered response _ final reached
    reward forfeit forfeitNonnegative deposit depositNonnegative (fun actual => PMF.pure actual)
  have same := response_result_same_information weight nonnegative decision recovered
    compatible.2.1 compatible.2.2 response
  rwa [← same] at upper

theorem responseValue_le_bestAnswerValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    responseValue weight nonnegative site representative decision current reward forfeit deposit
      assessment response ≤ bestAnswerValue weight nonnegative site reward forfeit deposit
        assessment :=
  (responseValue_le_scoreValue weight nonnegative site representative decision current reward
    forfeit deposit forfeitNonnegative depositNonnegative assessment response).trans
      (response_score_value_le_bestAnswerValue weight nonnegative site representative decision
        current reward forfeit deposit assessment response)

theorem incumbent_value_eq_response_average
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
    expect (currentResponses weight nonnegative decision assessment)
      (responseValue weight nonnegative site representative decision current reward forfeit
        deposit assessment) := by
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  let utility := fun final : app.Execution => LateOpeningRuntimeNash.payoff reward forfeit
    (fun actual => PMF.pure actual) deposit (app.finished final) bob
  have bounded : ∀ final : app.Execution, |utility final| ≤ 1 + |forfeit| + |deposit bob| :=
    fun final => LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
      (fun actual => PMF.pure actual) deposit (app.finished final)
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (assessment.strategy bob))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [incumbent_context_outcome_law weight nonnegative site representative decision current,
    expect_map] at mapped
  have valueEq : (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
      expect (incumbentFinalLaw weight nonnegative site representative decision current assessment)
        utility := mapped.symm
  rw [valueEq]
  unfold incumbentFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded)]
  calc
    _ = expect (assessment.belief bob site) (fun history =>
        expect (currentResponses weight nonnegative decision assessment) (fun response =>
          expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14
            ((decisionOfInformation weight nonnegative site representative decision current
              history).execution.respond app bob response)) utility)) := by
      apply expect_congr_on_support
      intro history _
      have compatible := decisionOfInformation_spec weight nonnegative site representative decision
        current history
      unfold ReactiveApplication.invoke
      rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded), expect_map]
      rw [← compatible.2.1, ← compatible.2.2]
      rfl
    _ = _ := expect_comm_of_support_finite_left _ _ (Set.toFinite _) _ fun history _ =>
      payoffIntegrable_of_bounded _ _ fun response =>
        expect_abs_le_of_bounded (by positivity) bounded

include representative decision current in
theorem incumbent_value_le_bestAnswerValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) ≤
        bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  rw [incumbent_value_eq_response_average weight nonnegative site representative decision current]
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun response => responseValue_bounded weight nonnegative site
      representative decision current reward forfeit deposit assessment response)
  intro response _
  exact responseValue_le_bestAnswerValue weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment response

include representative decision current in
/-- At every timely successful-publication binding class, rationality attains
exactly the maximum of Safe and the three actual private-label masses. -/
theorem rational_value_eq_bestAnswerValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
        bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  apply le_antisymm (incumbent_value_le_bestAnswerValue weight nonnegative site representative
    decision current reward forfeit deposit forfeitNonnegative depositNonnegative assessment)
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      assessment alternative)).mp rational
  exact max_le
    (comparison (answerFinitePolicy weight nonnegative safe) (Set.mem_univ _))
    (max_le (comparison (answerFinitePolicy weight nonnegative (labelGuess 0)) (Set.mem_univ _))
      (max_le (comparison (answerFinitePolicy weight nonnegative (labelGuess 1)) (Set.mem_univ _))
        (comparison (answerFinitePolicy weight nonnegative (labelGuess 2)) (Set.mem_univ _))))

/-- Every supported raw first response attains the same maximal continuation
value. This conclusion concerns the actual strategy's response law. -/
theorem rational_supported_response_value (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ response ∈ (currentResponses weight nonnegative decision assessment).support,
      responseValue weight nonnegative site representative decision current reward forfeit deposit
        assessment response = bestAnswerValue weight nonnegative site reward forfeit deposit
          assessment := by
  apply expect_eq_const_of_le_on_support _ _ _
    (payoffIntegrable_of_bounded _ _ fun response => responseValue_bounded weight nonnegative site
      representative decision current reward forfeit deposit assessment response)
    (fun response _ => responseValue_le_bestAnswerValue weight nonnegative site representative
      decision current reward forfeit deposit forfeitNonnegative depositNonnegative assessment
        response)
  rw [← incumbent_value_eq_response_average weight nonnegative site representative decision current]
  exact rational_value_eq_bestAnswerValue weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational


include representative current in
/-- Every supported raw first response successfully binds a maximizing Safe
answer or private-label guess. Packet aliases remain part of the raw menu. -/
theorem rational_supported_binding (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ response ∈ (currentResponses weight nonnegative decision assessment).support,
      ∃ answer : Answer,
        (serviced decision.execution response).application.config.store (.inr bobBindEvent) =
          some (.success answer) ∧
        (answer = safe ∨ ∃ label : Fin 3, answer = labelGuess label) ∧
        (context weight nonnegative site reward forfeit deposit assessment).value
          (answerFinitePolicy weight nonnegative answer) =
            bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
  intro response supported
  have value := rational_supported_response_value weight nonnegative site representative decision
    current reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational
      response supported
  have ceiling := responseValue_le_scoreValue weight nonnegative site representative decision
    current reward forfeit deposit forfeitNonnegative depositNonnegative assessment response
  rw [value] at ceiling
  have positive := bestAnswerValue_ge_safe weight nonnegative site representative decision current
    reward forfeit deposit assessment
  cases selected : (serviced decision.execution response).application.config.store
      (.inr bobBindEvent) with
  | none =>
      rw [selected] at ceiling
      simp only [bindingScore, expect_constant] at ceiling
      linarith
  | some result =>
      cases result with
      | failure =>
          rw [selected] at ceiling
          simp only [bindingScore, expect_constant] at ceiling
          linarith
      | success answer =>
          rw [selected] at ceiling
          change _ ≤ expect (assessment.belief bob site) (fun history =>
            answerScore (originalLabel (decisionOfInformation weight nonnegative site representative
              decision current history).execution) answer) at ceiling
          rw [← answer_context_value weight nonnegative site representative decision current
            reward forfeit deposit assessment answer] at ceiling
          have maximizing := le_antisymm
            (answer_value_le_bestAnswerValue weight nonnegative site representative decision
              current reward forfeit deposit assessment answer) ceiling
          have low : answer.val ≤ 3 := by
            by_contra contrary
            have high : 4 ≤ answer.val := by omega
            have zero := answer_context_value_eq_zero_of_high weight nonnegative site representative
              decision current reward forfeit deposit assessment answer high
            rw [zero] at maximizing
            linarith
          exact ⟨answer, rfl, answer_safe_or_label_of_low answer low, maximizing⟩

end Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization
