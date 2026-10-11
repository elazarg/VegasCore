/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstResponse
import Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality

/-! # Fixed collateral and both actual final Alice response laws

Forfeit and audit deposit are fixed before the public scheduler is chosen.
If both exceed the maximum gross reward, one finite lottery weight makes
sequential rationality force a genuine final opening when Alice has sent
nothing, and no second packet when her genuine first opening is pending.
The same scheduler satisfies the complete raw service contract and erasure
independence, while its canonical late omission probability stays strictly
positive and can be made smaller than any requested positive bound.

These are local response laws in the existing native game, not preservation
or exclusion of a complete sequential equilibrium.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- A predicate on the existing native strategy; it introduces no game or
alternative equilibrium notion. -/
def PendingResponsesNormalized
    (profile : ∀ who, (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy who) :
    Prop :=
  ∀ (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite alice)
      (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
        alice site.1)
      (decision : LateOpeningRuntimeAliceDecision.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨18, some alice, decision.execution⟩ →
        ((LateOpeningRuntimeAliceRationality.responseLaw weight nonnegative site
          (profile alice)).toOuterMeasure {response | response.transmission.isSome}).toReal = 0

def EmptyResponsesNormalized
    (profile : ∀ who, (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy who) :
    Prop :=
  ∀ (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite alice)
      (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
        alice site.1)
      (decision : LateOpeningRuntimeAliceEmptyDecision.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨18, some alice, decision.execution⟩ →
        ((LateOpeningRuntimeAliceOpeningRationality.responseLaw weight nonnegative site
          (profile alice)).toOuterMeasure {response |
            ¬ LateOpeningRuntimeAliceOpeningRationality.GenuineResponse
              weight nonnegative decision response}).toReal = 0

def LastAliceResponsesNormalized
    (profile : ∀ who, (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy who) :
    Prop :=
  PendingResponsesNormalized weight nonnegative profile ∧
    EmptyResponsesNormalized weight nonnegative profile

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem sequentially_rational_last_responses
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    LastAliceResponsesNormalized weight nonnegative assessment.strategy := by
  have retryMargin :
      0 < LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit := by
    unfold LateOpeningRuntimeAliceOpeningRationality.margin at marginPositive
    unfold LateOpeningRuntimeAliceRationality.margin
    linarith [min_le_right forfeit (deposit alice)]
  constructor
  · intro site representative decision current
    exact LateOpeningRuntimeAliceRationality.sequentially_rational_second_packet_zero
      weight nonnegative site representative decision current reward forfeit deposit positive
        rewardNonnegative forfeitNonnegative depositNonnegative retryMargin assessment rational
  · intro site representative decision current
    exact LateOpeningRuntimeAliceOpeningRationality.sequentially_rational_nongenuine_response_zero
      weight nonnegative site representative decision current reward forfeit deposit positive
        rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment rational
end Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization

namespace Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeService

def FirstResponsesNormalized (weight : ℝ) (nonnegative : 0 ≤ weight)
    (profile : ∀ who, (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy who) :
    Prop :=
  ∀ (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite alice)
      (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
        alice site.1)
      (decision : LateOpeningRuntimeAliceFirstDecision.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨22, some alice, decision.execution⟩ →
        ((LateOpeningRuntimeAliceFirstResponse.responseLaw weight nonnegative site
          (profile alice site.1)).toOuterMeasure {response |
            ¬ LateOpeningRuntimeAliceFirstResponse.PermittedResponse
              weight nonnegative decision response}).toReal = 0

def ResponsesNormalized (weight : ℝ) (nonnegative : 0 ≤ weight)
    (profile : ∀ who, (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy who) :
    Prop :=
  LastAliceResponsesNormalized weight nonnegative profile ∧
    FirstResponsesNormalized weight nonnegative profile

end Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization

namespace Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeAliceContinuation
open LateOpeningRuntimeAliceRationality
  (sequentially_rational_second_packet_zero_of_continuation_margin)
open LateOpeningRuntimeAliceOpeningRationality
  (sequentially_rational_nongenuine_response_zero_of_continuation_margin)
variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem sequentially_rational_last_responses_of_continuation_margin
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitPositive : 0 < forfeit) (bobDepositPositive : 0 < deposit bob)
    (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < continuationMargin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    LastAliceResponsesNormalized weight nonnegative
      assessment.strategy := by
  constructor
  · intro site representative decision current
    exact sequentially_rational_second_packet_zero_of_continuation_margin
      weight nonnegative site representative decision
      current reward forfeit deposit positive rewardNonnegative forfeitPositive bobDepositPositive
      depositNonnegative marginPositive assessment rational
  · intro site representative decision current
    exact sequentially_rational_nongenuine_response_zero_of_continuation_margin
      weight nonnegative site representative decision current reward forfeit deposit positive
      rewardNonnegative forfeitPositive bobDepositPositive depositNonnegative marginPositive
      assessment rational


end Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization
