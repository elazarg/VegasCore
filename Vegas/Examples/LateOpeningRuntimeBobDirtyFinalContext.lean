/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobRationality

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeBobDirtyFinalContext
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobService
  LateOpeningRuntimeBobInformation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (executionTrace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
    (some ⟨6, some bob, execution⟩))
  (current : representative.1.state = some ⟨6, some bob, execution⟩)

include current in
theorem site_information : site.1 = some (execution.recall bob, execution.observe app bob) := by
  rw [← representative.2]
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace = _
  rw [rawMenu.info, current]
  rfl

def openingChoice : (LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1 := by
  let response := LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
    (execution.recall bob)
    (execution.observe app bob) bobRevealEvent true
  refine ⟨some response, ?_⟩
  rw [site_information weight nonnegative site representative execution current]
  refine ⟨response, ?_, rfl⟩
  exact LateOpeningRuntimeBobResponseMenu.opening_available weight nonnegative
    LateOpeningRuntimeBobInformation.output_values_covered ⟨6, some bob, execution⟩
      (current ▸ representative.1.trace) rfl

def openingPolicy
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob := by
  classical
  exact (assessment.strategy bob).commit site.1
    (openingChoice weight nonnegative site representative execution current)

def finalLaw (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    PMF app.Execution :=
  (assessment.belief bob site).bind fun history =>
    ((alternative site.1).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
      app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) (fun _ =>
        app.silentPolicy) 6
        ((executionOfInformation weight nonnegative site representative execution executionTrace
          current history).respond app bob response)

theorem current_continuation_law
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom profile
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
      ((profile bob site.1).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) (fun _ =>
          app.silentPolicy) 6
          ((executionOfInformation weight nonnegative site representative execution executionTrace
            current history).respond app bob response)).map app.finished := by
  let recovered := executionOfInformation weight nonnegative site representative execution
    executionTrace current history
  have valid := executionOfInformation_spec weight nonnegative site representative execution
    executionTrace current history
  obtain ⟨rawTrace⟩ := valid.2.1
  have last := rawMenu.run_last_response initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 20 (final_passive weight nonnegative)
      profile history.1 bob 6 recovered valid.1 (by
        rw [final_cursor weight nonnegative recovered rawTrace])
  rw [history.2] at last
  exact last

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    ((LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
      (fun actual => PMF.pure actual) deposit assessment).outcome alternative).map History.state =
    (finalLaw weight nonnegative site representative execution executionTrace current assessment
      alternative).map app.finished := by
  dsimp only [LateOpeningRuntimeBobRationality.context,
    InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, finalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  rw [current_continuation_law weight nonnegative site representative execution executionTrace
    current, PMF.map_bind, Profile.update_same]

theorem context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    (LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
      (fun actual => PMF.pure actual) deposit assessment).value alternative =
    expect (finalLaw weight nonnegative site representative execution executionTrace current
      assessment alternative) (fun final => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) bob) := by
  have mapped := expect_map History.state
    ((LateOpeningRuntimeBobRationality.context weight nonnegative site reward forfeit
      (fun actual => PMF.pure actual) deposit assessment).outcome alternative)
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [context_outcome_law weight nonnegative site representative execution executionTrace current,
    expect_map] at mapped
  exact mapped.symm
end Vegas.Examples.LateOpeningRuntimeBobDirtyFinalContext
