/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding
import Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeAllOrNoneCleanBinding
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeUtility
open LateOpeningRuntimeAllOrNoneTrafficAudit LateOpeningRuntimeAllOrNoneBinding
open LateOpeningRuntimeBobSuccessInformation LateOpeningRuntimeBobSuccessDecision
  LateOpeningRuntimeBobSuccessPayoff LateOpeningRuntimeBobSuccessOptimization
  LateOpeningRuntimeEarlyBobSafeMenu
open LateOpeningRuntimeBobBindingDecision (context context_integrable answerPlayers)

theorem clean_answer_context_value
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (decision : LateOpeningRuntimeBobSuccessInformation.DecisionHistory weight weightNonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (answer : Answer) :
    (assessment.truncatedContinuationContext site
      (fun history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability nonnegative bounded) deposit history.state bob)
      (2 * LateOpeningRuntimeService.horizon + 1)).value
        (answerFinitePolicy weight weightNonnegative answer) =
      expect (assessment.belief bob site) (fun history =>
        answerScore (originalLabel (decisionOfInformation weight weightNonnegative site
          representative decision current history).execution) answer) := by
  let auditContext := assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability nonnegative bounded) deposit history.state bob)
    (2 * LateOpeningRuntimeService.horizon + 1)
  have mapped := expect_map History.state
    ((context weight weightNonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight weightNonnegative answer))
    (fun state => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability nonnegative bounded)
      deposit state bob)
  rw [answer_context_outcome_law weight weightNonnegative site representative decision current,
    expect_map] at mapped
  have nativeValue : auditContext.value
      (answerFinitePolicy weight weightNonnegative answer) =
      expect (answerFinalLaw weight weightNonnegative site representative decision current
        assessment answer) (fun final => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability nonnegative bounded) deposit (app.finished final) bob) := mapped.symm
  rw [nativeValue]
  unfold answerFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
      (sample probability nonnegative bounded)
      deposit (app.finished final))]
  apply expect_congr_on_support
  intro history _
  let recovered :=
    decisionOfInformation weight weightNonnegative site representative decision current history
  calc
    _ = expect _ (fun _ => answerScore (originalLabel recovered.execution) answer) := by
      apply expect_congr_on_support
      intro final reached
      exact answer_continuation_payoff weight weightNonnegative recovered answer
        (answerPlayers weight weightNonnegative assessment answer)
        (by simp only [answerPlayers, Function.update_self]) reward forfeit deposit
        (sample probability nonnegative bounded)
        (sample_authentic probability nonnegative bounded) final reached
    _ = _ := expect_constant _ _

theorem clean_binding_full_value_le_bestAnswerValue
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (decision : LateOpeningRuntimeBobSuccessInformation.DecisionHistory weight weightNonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (choice : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralPolicy bob) :
    (context weight weightNonnegative site reward forfeit deposit assessment).value choice ≤
      bestAnswerValue weight weightNonnegative site reward forfeit deposit assessment := by
  let changedStrategy := Profile.update
    (sig := (LateOpeningRuntimeGame.model weight weightNonnegative).behavioralSignature)
    assessment.strategy bob choice
  let changed : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment :=
    { assessment with strategy := changedStrategy }
  have upper := incumbent_value_le_bestAnswerValue weight weightNonnegative site representative
    decision current reward forfeit deposit forfeitNonnegative collateral changed
  have valueEq : (context weight weightNonnegative site reward forfeit deposit changed).value
      (changed.strategy bob) =
      (context weight weightNonnegative site reward forfeit deposit assessment).value choice := by
    simp only [context, changed, changedStrategy,
      InformationModel.BehavioralAssessment.truncatedContinuationContext,
      InformationModel.BehavioralAssessment.continuationContextWith, Context.value,
      GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner,
      Profile.update_same, Profile.update_idem]
  have bestEq : bestAnswerValue weight weightNonnegative site reward forfeit deposit changed =
      bestAnswerValue weight weightNonnegative site reward forfeit deposit assessment := by
    simp only [bestAnswerValue,
      answer_context_value weight weightNonnegative site representative decision current]
    rfl
  rwa [valueEq, bestEq] at upper


theorem clean_binding_rationality_scaled
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationHistory
      bob site.1)
    (decision : LateOpeningRuntimeBobSuccessInformation.DecisionHistory weight weightNonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.truncatedContinuationContext site
        (fun history => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability nonnegative bounded) deposit history.state bob)
        (2 * LateOpeningRuntimeService.horizon + 1))) :
    assessment.IsSequentiallyRationalAt site
      (context weight weightNonnegative site reward forfeit
        (fun owner => probability * deposit owner) assessment) := by
  let scaled := fun owner => probability * deposit owner
  let auditContext := assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability nonnegative bounded) deposit history.state bob)
    (2 * LateOpeningRuntimeService.horizon + 1)
  have integrable (choice) : auditContext.IntegrableAt choice :=
    payoffIntegrable_of_bounded _ _ fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
        (sample probability nonnegative bounded) deposit history.state
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy bob)) (fun choice _ => integrable choice)).mp rational
  have answerEq (answer : Answer) :
      auditContext.value (answerFinitePolicy weight weightNonnegative answer) =
      (context weight weightNonnegative site reward forfeit scaled assessment).value
        (answerFinitePolicy weight weightNonnegative answer) := by
    rw [clean_answer_context_value probability nonnegative bounded weight weightNonnegative
      site representative decision current reward forfeit deposit assessment,
      answer_context_value weight weightNonnegative site representative decision current]
  have lower : bestAnswerValue weight weightNonnegative site reward forfeit scaled assessment ≤
      auditContext.value (assessment.strategy bob) := by
    unfold bestAnswerValue
    apply max_le
    · rw [← answerEq safe]
      exact comparison _ (Set.mem_univ _)
    · apply max_le
      · rw [← answerEq (labelGuess 0)]
        exact comparison _ (Set.mem_univ _)
      · apply max_le
        · rw [← answerEq (labelGuess 1)]
          exact comparison _ (Set.mem_univ _)
        · rw [← answerEq (labelGuess 2)]
          exact comparison _ (Set.mem_univ _)
  have dominated := context_value_le_scaled probability nonnegative bounded weight
    weightNonnegative reward forfeit deposit collateral assessment
    ((LateOpeningRuntimeGame.model weight weightNonnegative).truncatedRunner
      (2 * LateOpeningRuntimeService.horizon + 1)) site (assessment.strategy bob)
  apply (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight weightNonnegative site reward forfeit scaled assessment
      (assessment.strategy bob))
    (fun choice _ => context_integrable weight weightNonnegative site reward forfeit scaled
      assessment choice)).mpr
  intro choice _
  exact (clean_binding_full_value_le_bestAnswerValue weight weightNonnegative site representative
    decision current reward forfeit scaled forfeitNonnegative (mul_nonneg nonnegative collateral)
      assessment choice).trans (lower.trans dominated)


end Vegas.Examples.LateOpeningRuntimeAllOrNoneCleanBinding
