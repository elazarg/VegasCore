/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeAllOrNoneAlice
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeUtility
open LateOpeningRuntimeAllOrNoneTrafficAudit

theorem payoff_eq (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (state : app.ProtocolState) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability nonnegative bounded)
        deposit state alice =
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner) state alice := by
  cases state with
  | some control =>
    exact alice_payoff probability nonnegative bounded reward forfeit deposit control
  | none =>
    simp [LateOpeningRuntimeGame.payoff, TerminalAudit.utility, TerminalAudit.charge,
      EventGraphRuntime.serviceAuditObservation, serviceSourceAudit,
      EventGraphRuntime.serviceAudit, PMF.pure_map]

theorem continuation_context_eq (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (run : (LateOpeningRuntimeGame.model weight weightNonnegative).ContinuationRunner)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite alice) :
    assessment.continuationContextWith run site
        (fun history => LateOpeningRuntimeGame.payoff reward forfeit
          (sample probability nonnegative bounded) deposit history.state alice) =
      assessment.continuationContextWith run site
        (fun history => LateOpeningRuntimeGame.payoff reward forfeit
          (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
          history.state alice) := by
  congr 1
  funext history
  exact payoff_eq probability nonnegative bounded reward forfeit deposit history.state

/-- Every Alice whole-policy comparison keeps its value and integrability guards. -/
theorem rational_at_iff (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (run : (LateOpeningRuntimeGame.model weight weightNonnegative).ContinuationRunner)
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite alice) :
    assessment.IsSequentiallyRationalAt site
        (assessment.continuationContextWith run site
          (fun history => LateOpeningRuntimeGame.payoff reward forfeit
            (sample probability nonnegative bounded) deposit history.state alice)) ↔
      assessment.IsSequentiallyRationalAt site
        (assessment.continuationContextWith run site
          (fun history => LateOpeningRuntimeGame.payoff reward forfeit
            (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
            history.state alice)) := by
  rw [continuation_context_eq probability nonnegative bounded weight weightNonnegative
    reward forfeit deposit assessment run site]

theorem rational_alice (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (weight : ℝ) (weightNonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeGame.model weight weightNonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight weightNonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability nonnegative bounded) deposit history.state who))
    (site : (LateOpeningRuntimeGame.model weight weightNonnegative).InformationSite alice) :
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight weightNonnegative)).wellFoundedHistories
        site (fun history => LateOpeningRuntimeGame.payoff reward forfeit
          (fun actual => PMF.pure actual) (fun owner => probability * deposit owner)
          history.state alice)) := by
  exact (rational_at_iff probability nonnegative bounded weight weightNonnegative
    reward forfeit deposit assessment _ site).mp (rational alice site)

end Vegas.Examples.LateOpeningRuntimeAllOrNoneAlice
