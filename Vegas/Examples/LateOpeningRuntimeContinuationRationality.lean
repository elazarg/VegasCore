/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeGame

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeContinuationRationality
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def AliceContinuationsRational
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (payoff : app.ProtocolState → Player → ℝ) : Prop :=
  ∀ site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite alice,
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
        site (fun history => payoff history.state alice))

/-- Only actual live binding and already-bound receiver callbacks are required.
The original assessment, complete compatible histories, and policies are retained. -/
def ReceiverContinuationsRational
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (payoff : app.ProtocolState → Player → ℝ) : Prop :=
  ∀ (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
      bob site.1) (control : app.Control),
    representative.1.state = some control → control.actor = some bob →
    ((control.remaining = 14 ∧ control.execution.application.config.cut.Ready bobBindEvent ∧
      control.execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent) ∨
      (control.remaining = 12 ∨ control.remaining = 6) ∧
        ∃ answer : Answer, control.execution.application.config.store (.inr bobBindEvent) =
          some (.success answer)) →
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
        site (fun history => payoff history.state bob))

theorem continuations_rational_of_rational
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (payoff : app.ProtocolState → Player → ℝ)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => payoff history.state who)) :
    AliceContinuationsRational weight nonnegative assessment payoff ∧
      ReceiverContinuationsRational weight nonnegative assessment payoff := by
  constructor
  · exact rational alice
  · intro site _ _ _ _ _
    exact rational bob site

end Vegas.Examples.LateOpeningRuntimeContinuationRationality
