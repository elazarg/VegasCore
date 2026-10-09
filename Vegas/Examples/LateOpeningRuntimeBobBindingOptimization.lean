/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobRawPayoff
import Vegas.Examples.LateOpeningRuntimeBobKnownBit

/-! # Optimal raw binding values under the actual posterior

After Alice's publication fails, every raw response is bounded by the score
of the one answer it fixes throughout the full information class. The two
clean fixed-bit policies attain complementary scores. Thus sequential
rationality gives the maximum of their actual assessment values, without
assuming a prior or excluding sampled pending contents from information.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingOptimization

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobBindingDecision LateOpeningRuntimeBobAnswerPayoff
  LateOpeningRuntimeBobRawBinding LateOpeningRuntimeBobRawPayoff
  LateOpeningRuntimeBobKnownBit LateOpeningRuntimeEarlyBobSafeMenu

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

def bestGuessValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) : ℝ :=
  max ((context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative (bitGuess false)))
    ((context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative (bitGuess true)))

include representative decision current in
theorem bestGuessValue_ge_half
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (1 / 2 : ℝ) ≤ bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  obtain ⟨bit, lower⟩ := exists_bit_guess_value_ge_half weight nonnegative site representative
    decision current reward forfeit deposit assessment
  cases bit
  · exact lower.trans (le_max_left _ _)
  · exact lower.trans (le_max_right _ _)

include representative decision current in
theorem answer_value_le_bestGuessValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) ≤
        bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  by_cases left : answer.val = 4
  · have same : answer = bitGuess false := Subtype.ext left
    rw [same]
    exact le_max_left _ _
  by_cases right : answer.val = 5
  · have same : answer = bitGuess true := Subtype.ext right
    rw [same]
    exact le_max_right _ _
  have valueZero : (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) = 0 := by
    rw [answer_context_value weight nonnegative site representative decision current]
    calc
      _ = expect (assessment.belief bob site) (fun _ => (0 : ℝ)) := by
        apply expect_congr_on_support
        intro history _
        cases originalBit (decisionOfInformation weight nonnegative site representative decision
          current history).execution
        · change (if answer.val = 4 then (1 : ℝ) else 0) = 0
          rw [ite_eq_right left]
        · change (if answer.val = 5 then (1 : ℝ) else 0) = 0
          rw [ite_eq_right right]
      _ = 0 := expect_constant _ _
  rw [valueZero]
  linarith [bestGuessValue_ge_half weight nonnegative site representative decision current
    reward forfeit deposit assessment]

private theorem score_abs_le_one (bit : Bool) (result : Option (PublicationResult Answer)) :
    |bindingScore bit result| ≤ 1 := by
  cases result with
  | none => norm_num [bindingScore]
  | some result =>
      cases result with
      | failure => norm_num [bindingScore]
      | success answer =>
          change |if answer.val = (if bit then 5 else 4) then (1 : ℝ) else 0| ≤ 1
          split_ifs <;> norm_num

include representative decision current in
/-- The expected ceiling of any fixed raw response is bounded by the two
actual clean bit-guess values at this information class. -/
theorem response_score_value_le_bestGuessValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    expect (assessment.belief bob site) (fun history =>
      bindingScore (originalBit (decisionOfInformation weight nonnegative site representative
        decision current history).execution)
          ((serviced decision.execution response).application.config.store (.inr bobBindEvent))) ≤
      bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  cases selected : (serviced decision.execution response).application.config.store
      (.inr bobBindEvent) with
  | none =>
      simp only [bindingScore, expect_constant]
      linarith [bestGuessValue_ge_half weight nonnegative site representative decision current
        reward forfeit deposit assessment]
  | some result =>
      cases result with
      | failure =>
          simp only [bindingScore, expect_constant]
          linarith [bestGuessValue_ge_half weight nonnegative site representative decision current
            reward forfeit deposit assessment]
      | success answer =>
          change expect (assessment.belief bob site) (fun history =>
            if answer.val = (if originalBit (decisionOfInformation weight nonnegative site
              representative decision current history).execution then 5 else 4) then 1 else 0) ≤ _
          rw [← answer_context_value weight nonnegative site representative decision current
            reward forfeit deposit assessment answer]
          exact answer_value_le_bestGuessValue weight nonnegative site representative decision
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
        bindingScore (originalBit (decisionOfInformation weight nonnegative site representative
          decision current history).execution)
            ((serviced decision.execution response).application.config.store
              (.inr bobBindEvent))) := by
  apply expect_mono _
    (payoffIntegrable_of_bounded _ _ fun history => by
      apply expect_abs_le_of_bounded (show 0 ≤ 1 + |forfeit| + |deposit bob| by positivity)
      intro final
      exact LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final))
    (payoffIntegrable_of_bounded _ _ fun history => score_abs_le_one _ _)
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

theorem responseValue_le_bestGuessValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    responseValue weight nonnegative site representative decision current reward forfeit deposit
      assessment response ≤ bestGuessValue weight nonnegative site reward forfeit deposit
        assessment :=
  (responseValue_le_scoreValue weight nonnegative site representative decision current reward
    forfeit deposit forfeitNonnegative depositNonnegative assessment response).trans
      (response_score_value_le_bestGuessValue weight nonnegative site representative decision
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
theorem incumbent_value_le_bestGuessValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) ≤
        bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  rw [incumbent_value_eq_response_average weight nonnegative site representative decision current]
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun response => responseValue_bounded weight nonnegative site
      representative decision current reward forfeit deposit assessment response)
  intro response _
  exact responseValue_le_bestGuessValue weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment response

include representative decision current in
/-- At every actual failed-publication binding class, sequential rationality
attains exactly the better of the two actual fixed-bit guess values. -/
theorem rational_value_eq_bestGuessValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
        bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  apply le_antisymm (incumbent_value_le_bestGuessValue weight nonnegative site representative
    decision current reward forfeit deposit forfeitNonnegative depositNonnegative assessment)
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      assessment alternative)).mp rational
  exact max_le
    (comparison (answerFinitePolicy weight nonnegative (bitGuess false)) (Set.mem_univ _))
    (comparison (answerFinitePolicy weight nonnegative (bitGuess true)) (Set.mem_univ _))

/-- Every supported raw first response attains the same maximal continuation
value. This conclusion concerns the actual strategy's response law. -/
theorem rational_supported_response_value (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ response ∈ (currentResponses weight nonnegative decision assessment).support,
      responseValue weight nonnegative site representative decision current reward forfeit deposit
        assessment response = bestGuessValue weight nonnegative site reward forfeit deposit
          assessment := by
  apply expect_eq_const_of_le_on_support _ _ _
    (payoffIntegrable_of_bounded _ _ fun response => responseValue_bounded weight nonnegative site
      representative decision current reward forfeit deposit assessment response)
    (fun response _ => responseValue_le_bestGuessValue weight nonnegative site representative
      decision current reward forfeit deposit forfeitNonnegative depositNonnegative assessment
        response)
  rw [← incumbent_value_eq_response_average weight nonnegative site representative decision current]
  exact rational_value_eq_bestGuessValue weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational

include representative current in
/-- Supported raw first responses successfully bind a maximizing bit guess.
Private packet aliases remain allowed by this logical-answer conclusion. -/
theorem rational_supported_binding (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ response ∈ (currentResponses weight nonnegative decision assessment).support,
      ∃ bit : Bool,
        (serviced decision.execution response).application.config.store (.inr bobBindEvent) =
          some (.success (bitGuess bit)) ∧
        (context weight nonnegative site reward forfeit deposit assessment).value
          (answerFinitePolicy weight nonnegative (bitGuess bit)) =
            bestGuessValue weight nonnegative site reward forfeit deposit assessment := by
  intro response supported
  have value := rational_supported_response_value weight nonnegative site representative decision
    current reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational
      response supported
  have ceiling := responseValue_le_scoreValue weight nonnegative site representative decision
    current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment response
  rw [value] at ceiling
  have positive := bestGuessValue_ge_half weight nonnegative site representative decision current
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
            if answer.val = (if originalBit (decisionOfInformation weight nonnegative site
              representative decision current history).execution then 5 else 4) then 1 else 0)
            at ceiling
          rw [← answer_context_value weight nonnegative site representative decision current
            reward forfeit deposit assessment answer] at ceiling
          have maximizing := le_antisymm
            (answer_value_le_bestGuessValue weight nonnegative site representative decision current
              reward forfeit deposit assessment answer) ceiling
          by_cases left : answer.val = 4
          · have same : answer = bitGuess false := Subtype.ext left
            exact ⟨false, congrArg (fun answer => some (PublicationResult.success answer)) same,
              same ▸ maximizing⟩
          by_cases right : answer.val = 5
          · have same : answer = bitGuess true := Subtype.ext right
            exact ⟨true, congrArg (fun answer => some (PublicationResult.success answer)) same,
              same ▸ maximizing⟩
          have zero : (context weight nonnegative site reward forfeit deposit assessment).value
              (answerFinitePolicy weight nonnegative answer) = 0 := by
            rw [answer_context_value weight nonnegative site representative decision current]
            calc
              _ = expect (assessment.belief bob site) (fun _ => (0 : ℝ)) := by
                apply expect_congr_on_support
                intro history _
                cases originalBit (decisionOfInformation weight nonnegative site representative
                  decision current history).execution
                · change (if answer.val = 4 then (1 : ℝ) else 0) = 0
                  rw [ite_eq_right left]
                · change (if answer.val = 5 then (1 : ℝ) else 0) = 0
                  rw [ite_eq_right right]
              _ = 0 := expect_constant _ _
          linarith

end Vegas.Examples.LateOpeningRuntimeBobBindingOptimization
