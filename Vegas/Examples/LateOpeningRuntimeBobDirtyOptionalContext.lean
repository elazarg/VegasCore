/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeOptionalDecision

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalContext
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobService
  LateOpeningRuntimeOptionalInformation LateOpeningRuntimeEarlyBobSafeMenu
  LateOpeningRuntimeBobSafeContinuation
open LateOpeningRuntimeBobBindingDecision
  (answerPlayers answerPlayers_admissible answerProfile_as_restriction context context_integrable)
variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (executionTrace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
    (some ⟨12, some bob, execution⟩))
  (current : representative.1.state = some ⟨12, some bob, execution⟩)
  (answer : Answer)
  (ready : execution.application.config.cut.Ready bobRevealEvent)

def canonicalFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Execution :=
  (assessment.belief bob site).bind fun history =>
    let recovered := executionOfInformation weight nonnegative site representative execution
      executionTrace current history
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (answerPlayers weight nonnegative assessment answer) 12
      (recovered.respond app bob
        (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (recovered.recall bob) (recovered.observe app bob) bobRevealEvent true))

include ready in
theorem canonical_current_continuation_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom
      (Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
        assessment.strategy bob (answerFinitePolicy weight nonnegative answer))
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
    let recovered := executionOfInformation weight nonnegative site representative execution
      executionTrace current history
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (answerPlayers weight nonnegative assessment answer) 12
      (recovered.respond app bob
        (LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (recovered.recall bob) (recovered.observe app bob) bobRevealEvent true))).map
          app.finished := by
  let recovered := executionOfInformation weight nonnegative site representative execution
    executionTrace current history
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    executionTrace current history
  rw [answerProfile_as_restriction weight nonnegative]
  rw [rawMenu.run_restrict_eq_finish initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    (answerPlayers weight nonnegative assessment answer)
    (answerPlayers_admissible weight nonnegative assessment answer)
    _ history.1 (by rw [valid.1]; change 25 ≤ 53; decide), valid.1]
  have actualReady := LateOpeningRuntimeBobInformation.ready_same_view _ _ valid.2.2.2 ready
  obtain ⟨actualTrace⟩ := valid.2.1
  have clock : recovered.application.clock = 3 := by
    rw [clock_history weight nonnegative _ actualTrace]
    have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) actualTrace
    change recovered.environmentRecall.length + 12 = 26 at accounted
    have cursor : recovered.environmentRecall.length = 14 := by omega
    rw [cursor]
    rfl
  unfold ReactiveApplication.finish ReactiveApplication.resume ReactiveApplication.invoke
  change (((answerPlayers weight nonnegative assessment answer bob
    (recovered.recall bob) (recovered.observe app bob)).map
      (fun response => recovered.respond app bob response)).bind
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (answerPlayers weight nonnegative assessment answer) 12)).map app.finished = _
  simp only [answerPlayers, Function.update_self,
    answerPolicy_opening answer recovered actualReady clock, PMF.pure_map, PMF.pure_bind]
  rfl

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

include ready in
theorem canonical_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (answerFinitePolicy weight nonnegative answer)).map History.state =
    (canonicalFinalLaw weight nonnegative site representative execution executionTrace
      current answer
      assessment).map app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, canonicalFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  exact canonical_current_continuation_law weight nonnegative site representative execution
    executionTrace current answer ready assessment history

def incumbentFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Execution :=
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  (assessment.belief bob site).bind fun history =>
    (app.invoke players bob
      (executionOfInformation weight nonnegative site representative execution
        executionTrace current
        history)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 12)

theorem incumbent_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (assessment.strategy bob)).map History.state =
    (incumbentFinalLaw weight nonnegative site representative execution executionTrace current
      assessment).map app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, incumbentFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    executionTrace current history
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
end Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalContext
