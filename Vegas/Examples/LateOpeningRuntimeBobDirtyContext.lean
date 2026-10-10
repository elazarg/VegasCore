/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyAttainment
import Vegas.Examples.LateOpeningRuntimeBobBindingDecision

/-! # Whole answer deviation values after sunk receiver charges

The native bounded continuation context retains the entire legal information
fiber. Existing whole answer policies attain their logical scores, shifted by
the already incurred receiver audit deduction, at every compatible history.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobDirtyContext

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobSuccessPayoff LateOpeningRuntimeBobDirtyAttainment
  LateOpeningRuntimeBobBindingDecision LateOpeningRuntimeEarlyBobSafeMenu

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

def executionOfInformation
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    app.Execution := Classical.choose
      (LateOpeningRuntimeBobBindingFiber.binding_history_same_information weight nonnegative
        site representative execution (rawMenu.toRawTrace _ _ _ trace) ready current history)

theorem executionOfInformation_spec
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    history.1.state = some ⟨14, some bob,
      executionOfInformation weight nonnegative site representative execution trace ready
        current history⟩ ∧
      execution.recall bob =
        (executionOfInformation weight nonnegative site representative execution trace ready
          current history).recall bob ∧
      execution.observe app bob =
        (executionOfInformation weight nonnegative site representative execution trace ready
          current history).observe app bob := Classical.choose_spec
      (LateOpeningRuntimeBobBindingFiber.binding_history_same_information weight nonnegative
        site representative execution (rawMenu.toRawTrace _ _ _ trace) ready current history)

def answerFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) : PMF app.Execution :=
  (assessment.belief bob site).bind fun history =>
    let recovered := executionOfInformation weight nonnegative site representative execution
      trace ready current history
    (LateOpeningRuntimeBobSafeContinuation.answerPolicy answer
      (recovered.recall bob) (recovered.observe app bob)).bind fun response =>
        app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (answerPlayers weight nonnegative assessment answer) 14
            (recovered.respond app bob response)

theorem answer_current_continuation_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (answer : Answer) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom
      (Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
        assessment.strategy bob (answerFinitePolicy weight nonnegative answer))
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
    (let recovered := executionOfInformation weight nonnegative site representative execution
        trace ready current history;
      (LateOpeningRuntimeBobSafeContinuation.answerPolicy answer
        (recovered.recall bob) (recovered.observe app bob)).bind fun response =>
          app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
            (answerPlayers weight nonnegative assessment answer) 14
              (recovered.respond app bob response)).map app.finished := by
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    trace ready current history
  rw [answerProfile_as_restriction weight nonnegative]
  rw [rawMenu.run_restrict_eq_finish initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    (answerPlayers weight nonnegative assessment answer)
    (answerPlayers_admissible weight nonnegative assessment answer)
    _ history.1 (by rw [valid.1]; change 29 ≤ 53; decide), valid.1]
  unfold ReactiveApplication.finish ReactiveApplication.resume ReactiveApplication.invoke
  simp only [answerPlayers, Function.update_self, PMF.bind_map]
  rfl

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem answer_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative answer)).map History.state =
    (answerFinalLaw weight nonnegative site representative execution trace ready current
      assessment answer).map app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, answerFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  exact answer_current_continuation_law weight nonnegative site representative execution trace
    ready current assessment history answer

theorem answer_context_value
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (dirty : ¬ SilentRecall execution) (bit : Bool)
    (published : execution.application.config.store (.inr aliceEvent) =
      some (.success bit : PublicationResult Bool))
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (answer : Answer) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) =
    expect (assessment.belief bob site) fun history =>
      answerScore (originalLabel (executionOfInformation weight nonnegative site representative
        execution trace ready current history)) answer - deposit bob := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative answer))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [answer_context_outcome_law weight nonnegative site representative execution trace ready
    current, expect_map] at mapped
  have nativeValue : (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative answer) =
      expect (answerFinalLaw weight nonnegative site representative execution trace ready current
        assessment answer) (fun final => LateOpeningRuntimeNash.payoff reward forfeit
          (fun actual => PMF.pure actual) deposit (app.finished final) bob) := mapped.symm
  rw [nativeValue]
  unfold answerFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final))]
  apply expect_congr_on_support
  intro history _
  obtain ⟨other, serial, stateEq, selected, attained⟩ := dirty_information_answer_attainment
    weight nonnegative site representative execution trace ready timely dirty bit published current
      history reward forfeit deposit answer
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    trace ready current history
  have otherEq : other = executionOfInformation weight nonnegative site representative execution
      trace ready current history := by
    have equal := Option.some.inj (stateEq.symm.trans valid.1)
    exact congrArg ReactiveApplication.Control.execution equal
  subst other
  dsimp only
  rw [selected, PMF.pure_bind]
  calc
    _ = expect _ (fun _ => answerScore (originalLabel
        (executionOfInformation weight nonnegative site representative execution trace ready
          current history)) answer - deposit bob) := by
      apply expect_congr_on_support
      intro final reached
      exact attained (answerPlayers weight nonnegative assessment answer)
        (by simp only [answerPlayers, Function.update_self]) final reached
    _ = _ := expect_constant _ _

def incumbentFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Execution :=
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  (assessment.belief bob site).bind fun history =>
    (app.invoke players bob
      (executionOfInformation weight nonnegative site representative execution trace ready
        current history)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14)

theorem incumbent_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (assessment.strategy bob)).map History.state =
    (incumbentFinalLaw weight nonnegative site representative execution trace ready current
      assessment).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, incumbentFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    trace ready current
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
          (by rw [valid.1]; change 29 ≤ 53; decide)
    _ = _ := by rw [valid.1]; rfl


def currentResponses
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Action :=
  rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
      (execution.recall bob) (execution.observe app bob)

def responseValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) : ℝ :=
  expect (assessment.belief bob site) fun history =>
    expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) 14
      ((executionOfInformation weight nonnegative site representative execution trace ready
        current history).respond app bob response)) fun final =>
          LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
            deposit (app.finished final) bob

theorem incumbent_value_eq_response_average
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
    expect (currentResponses weight nonnegative execution assessment)
      (responseValue weight nonnegative site representative execution trace ready current
        reward forfeit
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
  rw [incumbent_context_outcome_law weight nonnegative site representative execution trace ready
    current,
    expect_map] at mapped
  have valueEq : (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
      expect (incumbentFinalLaw weight nonnegative site representative execution trace ready current
        assessment)
        utility := mapped.symm
  rw [valueEq]
  unfold incumbentFinalLaw
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded)]
  calc
    _ = expect (assessment.belief bob site) (fun history =>
        expect (currentResponses weight nonnegative execution assessment) (fun response =>
          expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14
            ((executionOfInformation weight nonnegative site representative execution trace ready
              current history).respond app bob response)) utility)) := by
      apply expect_congr_on_support
      intro history _
      have compatible := executionOfInformation_spec weight nonnegative site representative
        execution
        trace ready
        current history
      unfold ReactiveApplication.invoke
      rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded), expect_map]
      rw [← compatible.2.1, ← compatible.2.2]
      rfl
    _ = _ := expect_comm_of_support_finite_left _ _ (Set.toFinite _) _ fun history _ =>
      payoffIntegrable_of_bounded _ _ fun response =>
        expect_abs_le_of_bounded (by positivity) bounded

end Vegas.Examples.LateOpeningRuntimeBobDirtyContext
