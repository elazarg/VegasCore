/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalRationality
import Vegas.Examples.LateOpeningRuntimeBobFinalObservation

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalFiber
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService
  LateOpeningRuntimeOptionalInformation LateOpeningRuntimeBobDirtyOptionalContext
  LateOpeningRuntimeBobDirtyOptionalRationality LateOpeningRuntimeBobFinalObservation
open LateOpeningRuntimeBobBindingDecision (context)
variable (weight : ℝ) (nonnegative : 0 ≤ weight)
private def answerView (view : PlayerView nativeGraph) : Option (PublicationResult Answer) :=
  view.observation.store (.inr bobRevealEvent)
private theorem answerView_physical (physical : app.State) :
    answerView (physical.playerView bob) = physical.config.store (.inr bobRevealEvent) :=
  nativeGraph.playerStore_of_visible bob physical.config.store (.inr bobRevealEvent) (by decide)

theorem serviced_answer_same_information (first second : app.Execution)
    (firstTrace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨12, some bob, first⟩))
    (secondTrace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨12, some bob, second⟩))
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob) (response : app.Action) :
    (serviced first response).application.config.store (.inr bobRevealEvent) =
      (serviced second response).application.config.store (.inr bobRevealEvent) := by
  have physical := LateOpeningRuntimeBobResponseState.responseState_same_view first second
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) firstTrace)
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) secondTrace)
    sameRecall sameView response
  rw [serviced_physical weight nonnegative 12 first firstTrace response,
    serviced_physical weight nonnegative 12 second secondTrace response]
  exact (answerView_physical _).symm.trans
    ((congrArg answerView physical).trans (answerView_physical _))

theorem failure_persists (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨12, some bob, execution⟩))
    (response : app.Action)
    (failed : (serviced execution response).application.config.store (.inr bobRevealEvent) =
      some .failure) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 12 (execution.respond app bob response)).support) :
    final.application.config.store (.inr bobRevealEvent) = some .failure := by
  rw [ReactiveApplication.runRounds,
    serviced_round weight nonnegative 12 execution trace response players, PMF.pure_bind] at reached
  exact (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent) .failure)
    players).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 11 _ final
      failed reached

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (executionTrace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
    (some ⟨12, some bob, execution⟩))
  (current : representative.1.state = some ⟨12, some bob, execution⟩)
  (answer : Answer)
  (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
  (ready : execution.application.config.cut.Ready bobRevealEvent)
  (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
  (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
  (reward forfeit : ℝ) (deposit : Player → ℝ)
include representative executionTrace current bound ready timely rejected in
theorem rational_supported_response_not_failure (forfeitPositive : 0 < forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
      (execution.recall bob) (execution.observe app bob)).support) :
    (serviced execution response).application.config.store (.inr bobRevealEvent) ≠
      some .failure := by
  intro failed
  have zero := rational_optional_failure_zero weight nonnegative site representative execution
    executionTrace current answer bound ready timely serial rejected reward forfeit deposit
    forfeitPositive assessment rational
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  obtain ⟨history, believed⟩ := (assessment.belief bob site).support_nonempty
  let recovered := executionOfInformation weight nonnegative site representative execution
    executionTrace current history
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    executionTrace current history
  obtain ⟨actualTrace⟩ := valid.2.1
  have actualFailed := (serviced_answer_same_information weight nonnegative execution recovered
    executionTrace actualTrace valid.2.2.1 valid.2.2.2 response).symm.trans failed
  have actualSupported : response ∈ (players bob (recovered.recall bob)
      (recovered.observe app bob)).support := by
    rw [← valid.2.2.1, ← valid.2.2.2]
    exact supported
  obtain ⟨final, reached⟩ := (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 12 (recovered.respond app bob response)).support_nonempty
  have terminalFailure := failure_persists weight nonnegative recovered actualTrace response
    actualFailed players final reached
  have terminalSupported : final ∈ (incumbentFinalLaw weight nonnegative site representative
      execution executionTrace current assessment).support := by
    rw [incumbentFinalLaw, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨history, believed, ?_⟩
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨recovered.respond app bob response, ?_, reached⟩
    change (recovered.respond app bob response) ∈
      ((players bob (recovered.recall bob) (recovered.observe app bob)).map
        (fun action => recovered.respond app bob action)).support
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨response, actualSupported, rfl⟩
  have probabilityZero : (incumbentFinalLaw weight nonnegative site representative execution
      executionTrace current assessment).toOuterMeasure
      {last | last.application.config.store (.inr bobRevealEvent) = some .failure} = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp zero |>.resolve_right (outerMeasure_ne_top _ _)
  exact ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mp probabilityZero).le_bot
    ⟨terminalSupported, terminalFailure⟩
end Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalFiber
