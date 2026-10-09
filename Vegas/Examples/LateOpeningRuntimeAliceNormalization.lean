/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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

namespace Vegas.Examples.LateOpeningRuntimeAliceNormalization

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- A predicate on the existing native strategy; it introduces no game or
alternative equilibrium notion. -/
def LastAliceResponsesNormalized
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    Prop :=
  (∀ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        alice site.1)
      (decision : LateOpeningRuntimeAliceDecision.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨18, some alice, decision.execution⟩ →
        ((LateOpeningRuntimeAliceRationality.responseLaw weight nonnegative site
          (profile alice)).toOuterMeasure {response | response.transmission.isSome}).toReal = 0) ∧
  (∀ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        alice site.1)
      (decision : LateOpeningRuntimeAliceEmptyDecision.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨18, some alice, decision.execution⟩ →
        ((LateOpeningRuntimeAliceOpeningRationality.responseLaw weight nonnegative site
          (profile alice)).toOuterMeasure {response |
            ¬ LateOpeningRuntimeAliceOpeningRationality.GenuineResponse
              weight nonnegative decision response}).toReal = 0)

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem sequentially_rational_last_responses
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
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

theorem equilibrium_last_responses
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    LastAliceResponsesNormalized weight nonnegative assessment.strategy :=
  sequentially_rational_last_responses weight nonnegative reward forfeit deposit positive
    rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment equilibrium.1

omit weight nonnegative in
/-- Collateral precedes the builder. All actual information fibers of both
operational kinds share one strictly positive margin and one public scheduler. -/
theorem exists_service_with_last_responses_normalized
    (rewardNonnegative : 0 ≤ reward) (largeForfeit : reward < forfeit)
    (largeDeposit : reward < deposit alice) (failureFloor : ℝ) (floorPositive : 0 < failureFloor) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      0 < weight ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      0 < 1 - inclusionProbability weight ∧ 1 - inclusionProbability weight < failureFloor ∧
      0 < LateOpeningRuntimeAliceOpeningRationality.margin weight reward forfeit deposit ∧
      ∀ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentiallyRational
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
            (fun actual => PMF.pure actual) deposit history.state who) →
          LastAliceResponsesNormalized weight nonnegative assessment.strategy := by
  have totalPositive : 0 < forfeit + deposit alice := by linarith
  have gapPositive : 0 < min forfeit (deposit alice) - reward :=
    sub_pos.mpr (lt_min largeForfeit largeDeposit)
  let floor := min failureFloor ((min forfeit (deposit alice) - reward) /
    (forfeit + deposit alice))
  have positiveFloor : 0 < floor := lt_min floorPositive (div_pos gapPositive totalPositive)
  obtain ⟨weight, nonnegative, positive, contract, blind, receipts⟩ :=
    LateOpeningRuntimeTerminalReceipt.exists_joint_service_with_exact_failure floor positiveFloor
  obtain ⟨_, _, _, close⟩ := receipts false 0 0
  rw [LateOpeningRuntimeTerminalReceipt.terminal_receipt_probability] at close
  have scaled := mul_lt_mul_of_pos_right
    (close.trans_le (min_le_right failureFloor _)) totalPositive
  rw [div_mul_cancel₀ _ (ne_of_gt totalPositive)] at scaled
  have marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit := by
    unfold LateOpeningRuntimeAliceOpeningRationality.margin
    linarith
  refine ⟨weight, nonnegative, positive, contract, blind,
    sub_pos.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1),
    close.trans_le (min_le_left failureFloor _), marginPositive, ?_⟩
  intro assessment rational
  exact sequentially_rational_last_responses weight nonnegative reward forfeit deposit positive
    rewardNonnegative (by linarith) (by linarith) marginPositive assessment rational

end Vegas.Examples.LateOpeningRuntimeAliceNormalization
