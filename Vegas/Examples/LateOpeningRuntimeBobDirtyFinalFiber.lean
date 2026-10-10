/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyFinalRationality
import Vegas.Examples.LateOpeningRuntimeBobFinalObservation

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobDirtyFinalFiber
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobService LateOpeningRuntimeBobInformation
  LateOpeningRuntimeBobDirtyFinalContext LateOpeningRuntimeBobDirtyFinalRationality
  LateOpeningRuntimeBobFinalObservation
variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (executionTrace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some ⟨6, some bob, execution⟩))
  (current : representative.1.state = some ⟨6, some bob, execution⟩)

private def answerView (view : PlayerView nativeGraph) : Option (PublicationResult Answer) :=
  view.observation.store (.inr bobRevealEvent)

private theorem answerView_physical (physical : app.State) :
    answerView (physical.playerView bob) = physical.config.store (.inr bobRevealEvent) := by
  exact nativeGraph.playerStore_of_visible bob physical.config.store (.inr bobRevealEvent)
    (by decide)

theorem continuation_answer_same_information
    (first second : app.Execution)
    (firstTrace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some ⟨6, some bob, first⟩))
    (secondTrace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some ⟨6, some bob, second⟩))
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob)
    (response : app.Action) (firstPlayers secondPlayers : Player → app.Policy) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) firstPlayers 6
      (first.respond app bob response)).map
      (fun final => final.application.config.store (.inr bobRevealEvent)) =
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) secondPlayers 6
      (second.respond app bob response)).map
      (fun final => final.application.config.store (.inr bobRevealEvent)) := by
  have observed := continuation_owner_same_information weight nonnegative
    first second firstTrace secondTrace sameRecall
    sameView response firstPlayers secondPlayers
  have readout := congrArg (PMF.map answerView) observed
  simpa only [PMF.map_comp, Function.comp_def, answerView_physical] using readout

def responseContinuationLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : app.Execution) (players : Player → app.Policy) :
    PMF app.Execution :=
  ((assessment.strategy bob site.1).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 6
      (history.respond app bob response)

theorem finalLaw_answer_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (players : Player → app.Policy) :
    (finalLaw weight nonnegative site representative execution executionTrace current assessment
      (assessment.strategy bob)).map
        (fun final => final.application.config.store (.inr bobRevealEvent)) =
    (responseContinuationLaw weight nonnegative site assessment execution players).map
      (fun final => final.application.config.store (.inr bobRevealEvent)) := by
  unfold finalLaw
  rw [PMF.map_bind]
  calc
    _ = (assessment.belief bob site).bind (fun _ =>
        (responseContinuationLaw weight nonnegative site assessment execution players).map
          (fun final => final.application.config.store (.inr bobRevealEvent))) := by
      apply bind_congr_on_support _
      intro history _
      dsimp only [responseContinuationLaw]
      rw [PMF.map_bind, PMF.map_bind]
      apply bind_congr_on_support _
      intro response _
      have compatible := executionOfInformation_spec weight nonnegative site representative
        execution executionTrace current history
      obtain ⟨recoveredTrace⟩ := compatible.2.1
      exact continuation_answer_same_information weight nonnegative _ execution
        recoveredTrace executionTrace compatible.2.2.1.symm compatible.2.2.2.symm response _ players
    _ = _ := PMF.bind_const _ _

private theorem failure_probability_same (first second : PMF app.Execution)
    (same : first.map (fun final => final.application.config.store (.inr bobRevealEvent)) =
      second.map (fun final => final.application.config.store (.inr bobRevealEvent))) :
    (first.toOuterMeasure
      {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
    (second.toOuterMeasure
      {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal := by
  have mapped := congrArg (fun law : PMF (Option (PublicationResult Answer)) =>
    (law.toOuterMeasure {result | result = some .failure}).toReal) same
  simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using mapped

variable (answer : Answer)
  (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
  (ready : execution.application.config.cut.Ready bobRevealEvent)
  (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent)
  (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

include bound ready timely rejected in
theorem rational_every_history_failure_zero
    (forfeitPositive : 0 < forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
        (fun actual => PMF.pure actual) deposit assessment))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (players : Player → app.Policy) :
    ((responseContinuationLaw weight nonnegative site assessment
      (executionOfInformation weight nonnegative site representative execution
        executionTrace current
        history)
      players).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
          0 := by
  have assessed := rational_final_failure_zero weight nonnegative site representative execution
    executionTrace current answer bound ready timely serial rejected reward forfeit deposit
    forfeitPositive
      assessment rational
  have common := finalLaw_answer_law weight nonnegative site representative execution
    executionTrace current
    assessment players
  have compatible := executionOfInformation_spec weight nonnegative site representative execution
    executionTrace current history
  have fixed : (responseContinuationLaw weight nonnegative site assessment execution players).map
      (fun final => final.application.config.store (.inr bobRevealEvent)) =
    (responseContinuationLaw weight nonnegative site assessment
      (executionOfInformation weight nonnegative site representative execution
        executionTrace current
        history)
      players).map (fun final => final.application.config.store (.inr bobRevealEvent)) := by
    unfold responseContinuationLaw
    rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro response _
    obtain ⟨recoveredTrace⟩ := compatible.2.1
    exact continuation_answer_same_information weight nonnegative _ _ executionTrace recoveredTrace
      compatible.2.2.1
      compatible.2.2.2 response players players
  exact (failure_probability_same _ _ (common.trans fixed)).symm.trans assessed

include bound ready timely rejected in
theorem rational_supported_publication
    (forfeitPositive : 0 < forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
        (fun actual => PMF.pure actual) deposit assessment))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight
      nonnegative) players 6
      ((executionOfInformation weight nonnegative site representative execution
        executionTrace current
        history).respond app bob response)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) := by
  let recovered := executionOfInformation weight nonnegative site representative execution
    executionTrace current
    history
  have zero := rational_every_history_failure_zero weight nonnegative site representative execution
    executionTrace current answer bound ready timely serial rejected reward forfeit deposit
    forfeitPositive assessment
      rational history players
  have finalSupported : final ∈
      (responseContinuationLaw weight nonnegative site assessment recovered players).support := by
    rw [responseContinuationLaw, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨response, supported, reached⟩
  have probabilityZero : (responseContinuationLaw weight nonnegative site assessment recovered
      players).toOuterMeasure
      {last | last.application.config.store (.inr bobRevealEvent) = some .failure} = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp zero |>.resolve_right
      (outerMeasure_ne_top _ _)
  have noFailure : final.application.config.store (.inr bobRevealEvent) ≠ some .failure := by
    intro failure
    exact ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mp probabilityZero).le_bot
      ⟨finalSupported, failure⟩
  have compatible := executionOfInformation_spec weight nonnegative site representative execution
    executionTrace current history
  obtain ⟨recoveredTrace⟩ := compatible.2.1
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 6 recovered bob response recoveredTrace
  obtain ⟨terminalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 6 _ final responded reached
  have complete := (contract weight nonnegative).completes ⟨0, none, final⟩ terminalTrace ⟨rfl, rfl⟩
  obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal complete (.inr bobRevealEvent))
  cases result with
  | failure => exact (noFailure stored).elim
  | success opened =>
      obtain ⟨bit, label, invariant⟩ := history_initial_invariant
        LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)
        ⟨6, some bob, recovered⟩ recoveredTrace
      have actualBound := (bound_same_view _ _ compatible.2.2.2).symm.trans bound
      have same := bob_continuation_success_immutable LateOpeningRuntimeService.runtime leaks
        players (LateOpeningRuntimeService.scheduler weight nonnegative) 6 recovered final
        _ invariant answer actualBound response reached opened stored
      rw [same] at stored
      exact stored

end Vegas.Examples.LateOpeningRuntimeBobDirtyFinalFiber
