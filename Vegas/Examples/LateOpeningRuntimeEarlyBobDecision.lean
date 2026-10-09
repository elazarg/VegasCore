/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeEarlyBobInformation
import Vegas.Examples.LateOpeningRuntimeBobIncentive
import Interaction.ReactiveLocalContinuation

/-! # Whole native continuation after Bob's first response

A local response lottery executes one actual packet choice and retains the
incumbent policy at every later decision. The actual menu's decision recall
prevents the replaced information site from recurring. This gives exact
native values for quiet and rejected-packet comparisons under arbitrary
beliefs over the complete information class.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEarlyBobDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeEarlyBobAudit
  LateOpeningRuntimeEarlyBobInformation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨21, some bob, decision.execution⟩)

include current in
theorem site_information : site.1 =
    some (decision.execution.recall bob, decision.execution.observe app bob) := by
  rw [← representative.2]
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace = _
  rw [rawMenu.info, current]
  rfl

def quietChoice : (LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1 := by
  refine ⟨some (⟨none⟩ : app.Action), ?_⟩
  rw [site_information weight nonnegative site representative decision current]
  exact ⟨⟨none⟩, bounds.silent_available LateOpeningRuntimeService.runtime leaks bob _ _, rfl⟩

def localPolicy
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1)) :
    (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob := by
  classical
  exact (assessment.strategy bob).withLaw site.1 law

def quietPolicy
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob :=
  localPolicy weight nonnegative site assessment
    (PMF.pure (quietChoice weight nonnegative site representative decision current))

def responseLaw
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1)) :
    PMF app.Action := law.map (fun choice => choice.1.getD ⟨none⟩)

def continuation
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action) : PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) 21
    ((decisionOfInformation weight nonnegative site representative decision current
      history).execution.respond app bob response)

def finalLaw (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1)) :
    PMF app.Execution :=
  (assessment.belief bob site).bind fun history =>
    (responseLaw weight nonnegative site law).bind fun response =>
      continuation weight nonnegative site representative decision current assessment
        history response

theorem current_local_continuation_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1)) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom
      (Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
        assessment.strategy bob (localPolicy weight nonnegative site assessment law))
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
    (responseLaw weight nonnegative site law).bind fun response =>
      (continuation weight nonnegative site representative decision current assessment
        history response).map app.finished := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  have result := rawMenu.run_local_law_finish_of_information initial
    LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy history.1 bob 21
      recovered.execution valid.1 site.1 history.2 law 52 (by
        rw [valid.1]
        change 43 ≤ 53
        decide)
  refine result.trans ?_
  apply bind_congr_on_support _
  intro response _
  unfold ReactiveApplication.finish
  simp only [ReactiveApplication.resume, PMF.pure_bind]
  rfl

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

def context (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :=
  assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit history.state bob) (2 * LateOpeningRuntimeService.horizon + 1)

def utility (final : app.Execution) : ℝ :=
  LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
    (app.finished final) bob

theorem utility_bounded (final : app.Execution) :
    |utility reward forfeit deposit final| ≤ 1 + |forfeit| + |deposit bob| :=
  LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
    deposit (app.finished final)

theorem context_integrable
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    Context.IntegrableAt
      (context weight nonnegative site reward forfeit deposit assessment) alternative :=
  payoffIntegrable_of_bounded _ _ fun history =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
      deposit history.state

theorem local_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1)) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (localPolicy weight nonnegative site assessment law)).map History.state =
    (finalLaw weight nonnegative site representative decision current assessment law).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, finalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  rw [current_local_continuation_law weight nonnegative site representative decision current,
    PMF.map_bind]

theorem local_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (localPolicy weight nonnegative site assessment law) =
    expect (finalLaw weight nonnegative site representative decision current assessment law)
      (utility reward forfeit deposit) := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (localPolicy weight nonnegative site assessment law))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [local_context_outcome_law weight nonnegative site representative decision current,
    expect_map] at mapped
  exact mapped.symm

theorem incumbent_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
    expect (finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob site.1)) (utility reward forfeit deposit) := by
  have result := local_context_value weight nonnegative site representative decision current
    reward forfeit deposit assessment (assessment.strategy bob site.1)
  simpa only [localPolicy, InformationModel.BehavioralPolicy.withLaw_eq_self] using result

def responseValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) : ℝ :=
  expect ((assessment.belief bob site).bind fun history =>
    continuation weight nonnegative site representative decision current assessment history
      response)
    (utility reward forfeit deposit)

theorem finalLaw_response_first
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1)) :
    finalLaw weight nonnegative site representative decision current assessment law =
    (responseLaw weight nonnegative site law).bind fun response =>
      (assessment.belief bob site).bind fun history =>
        continuation weight nonnegative site representative decision current assessment
          history response := by
  unfold finalLaw
  exact PMF.bind_comm _ _ _

theorem local_context_value_response
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (localPolicy weight nonnegative site assessment law) =
    expect (responseLaw weight nonnegative site law)
      (responseValue weight nonnegative site representative decision current
        reward forfeit deposit assessment) := by
  rw [local_context_value weight nonnegative site representative decision current,
    finalLaw_response_first weight nonnegative site representative decision current]
  exact expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _
    (utility_bounded reward forfeit deposit))

theorem incumbent_context_value_response
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
    expect (responseLaw weight nonnegative site (assessment.strategy bob site.1))
      (responseValue weight nonnegative site representative decision current
        reward forfeit deposit assessment) := by
  have result := local_context_value_response weight nonnegative site representative decision
    current reward forfeit deposit assessment (assessment.strategy bob site.1)
  simpa only [localPolicy, InformationModel.BehavioralPolicy.withLaw_eq_self] using result

theorem quiet_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (quietPolicy weight nonnegative site representative decision current assessment) =
    responseValue weight nonnegative site representative decision current
      reward forfeit deposit assessment ⟨none⟩ := by
  rw [quietPolicy, local_context_value_response weight nonnegative site representative
    decision current]
  simp only [responseLaw, PMF.pure_map, quietChoice, Option.getD_some, expect_pure]

theorem rejected_responseValue_bound
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) (submitted : response.transmission.isSome) :
    responseValue weight nonnegative site representative decision current
      reward forfeit deposit assessment response ≤ 1 - deposit bob := by
  apply expect_le_const _ _ (payoffIntegrable_of_bounded _ _
    (utility_bounded reward forfeit deposit))
  intro final reached
  obtain ⟨history, _, sampled⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  obtain ⟨submission, sent⟩ := Option.isSome_iff_exists.mp submitted
  have responseEq : response = ⟨some submission⟩ := by cases response; cases sent; rfl
  exact early_submission_continuation_utility_bound forfeitNonnegative deposit depositNonnegative
    weight nonnegative recovered.execution recovered.trace submission recovered.unresolved
    (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) final
      (by simpa only [continuation, responseEq] using sampled)

end Vegas.Examples.LateOpeningRuntimeEarlyBobDecision
