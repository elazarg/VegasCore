/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeOptionalInformation
import Vegas.Examples.LateOpeningRuntimeOptionalIncentive
import Vegas.Examples.LateOpeningRuntimeBobBindingDecision

/-! # Whole-policy evaluation at the optional answer-opening callback

The unchanged bounded native menu contains the existing chosen-answer policy.
At every hidden history in one actual optional callback information class,
that policy opens the same immutable answer immediately and completes the
remaining physical execution. The incumbent law retains all original future
policies and all private response representations.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeOptionalDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeOptionalOpening
  LateOpeningRuntimeOptionalInformation LateOpeningRuntimeOptionalIncentive
  LateOpeningRuntimeBobSafeContinuation LateOpeningRuntimeEarlyBobSafeMenu
open LateOpeningRuntimeBobBindingDecision
  (answerPlayers answerPlayers_admissible answerProfile_as_restriction context context_integrable)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem decision_clock (decision : DecisionHistory weight nonnegative) :
    decision.execution.application.clock = 3 := by
  have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  change decision.execution.environmentRecall.length + 12 = 26 at counted
  have cursor : decision.execution.environmentRecall.length = 14 := by omega
  rw [clock_history weight nonnegative _ decision.trace, cursor]
  decide

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨12, some bob, decision.execution⟩)

def canonicalFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Execution :=
  (assessment.belief bob site).bind fun history =>
    let recovered := decisionOfInformation weight nonnegative site representative decision current
      history
    continuation weight nonnegative recovered (canonical weight nonnegative recovered)
      (answerPlayers weight nonnegative assessment decision.answer)

theorem canonical_current_continuation_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom
      (Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
        assessment.strategy bob (answerFinitePolicy weight nonnegative decision.answer))
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
    (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      (canonical weight nonnegative
        (decisionOfInformation weight nonnegative site representative decision current history))
      (answerPlayers weight nonnegative assessment decision.answer)).map app.finished := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  rw [answerProfile_as_restriction weight nonnegative]
  rw [rawMenu.run_restrict_eq_finish initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    (answerPlayers weight nonnegative assessment decision.answer)
    (answerPlayers_admissible weight nonnegative assessment decision.answer)
    _ history.1 (by rw [valid.1]; change 25 ≤ 53; decide), valid.1]
  unfold ReactiveApplication.finish ReactiveApplication.resume ReactiveApplication.invoke
  change (((answerPlayers weight nonnegative assessment decision.answer bob
    (recovered.execution.recall bob) (recovered.execution.observe app bob)).map
      (fun response => recovered.execution.respond app bob response)).bind
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (answerPlayers weight nonnegative assessment decision.answer) 12)).map app.finished = _
  simp only [answerPlayers, Function.update_self,
    answerPolicy_opening decision.answer recovered.execution recovered.ready
      (decision_clock weight nonnegative recovered), PMF.pure_map, PMF.pure_bind]
  rfl

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem canonical_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative decision.answer)).map History.state =
    (canonicalFinalLaw weight nonnegative site representative decision current assessment).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, canonicalFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  exact canonical_current_continuation_law weight nonnegative site representative decision current
    assessment history

def incumbentFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Execution :=
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  (assessment.belief bob site).bind fun history =>
    (app.invoke players bob
      (decisionOfInformation weight nonnegative site representative decision current
        history).execution).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 12)

theorem incumbent_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (assessment.strategy bob)).map History.state =
    (incumbentFinalLaw weight nonnegative site representative decision current assessment).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, incumbentFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  simp only [Profile.update, Function.update_eq_self]
  calc
    _ = app.finish initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)
        (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
        history.1.state :=
      rawMenu.run_eq_finish initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy 53 history.1
          (by rw [valid.1]; change 25 ≤ 53; decide)
    _ = _ := by rw [valid.1]; rfl

def currentResponses
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Action :=
  rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
      (decision.execution.recall bob) (decision.execution.observe app bob)

def conditionalValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ℝ :=
  expect (continuation weight nonnegative
    (decisionOfInformation weight nonnegative site representative decision current history)
    response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)) fun final =>
        LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
          deposit (app.finished final) bob

def canonicalValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ℝ :=
  let recovered := decisionOfInformation weight nonnegative site representative decision current
    history
  expect (continuation weight nonnegative recovered (canonical weight nonnegative recovered)
    (answerPlayers weight nonnegative assessment decision.answer)) fun final =>
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) bob

def responseValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) : ℝ :=
  expect (assessment.belief bob site) (conditionalValue weight nonnegative site representative
    decision current reward forfeit deposit assessment response)

theorem canonical_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative decision.answer) =
    expect (assessment.belief bob site) (canonicalValue weight nonnegative site representative
      decision current reward forfeit deposit assessment) := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative decision.answer))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [canonical_context_outcome_law weight nonnegative site representative decision current,
    expect_map] at mapped
  have valueEq : (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative decision.answer) =
      expect (canonicalFinalLaw weight nonnegative site representative decision current assessment)
        (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
          deposit (app.finished final) bob) := mapped.symm
  rw [valueEq]
  unfold canonicalFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final))]
  rfl

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
          expect (continuation weight nonnegative
            (decisionOfInformation weight nonnegative site representative decision current history)
            response players) utility)) := by
      apply expect_congr_on_support
      intro history _
      have compatible := decisionOfInformation_spec weight nonnegative site representative decision
        current history
      unfold ReactiveApplication.invoke
      rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded), expect_map]
      rw [← compatible.2.1, ← compatible.2.2.1]
      rfl
    _ = _ := expect_comm_of_support_finite_left _ _ (Set.toFinite _) _ fun history _ =>
      payoffIntegrable_of_bounded _ _ fun response =>
        expect_abs_le_of_bounded (by positivity) bounded

end Vegas.Examples.LateOpeningRuntimeOptionalDecision
