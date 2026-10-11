/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstRationality
import Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization
import Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality
import Vegas.Examples.LateOpeningRuntimeContinuationRationality

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
open LateOpeningRuntimeContinuationRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance
open LateOpeningRuntimeAliceResponseNormalization

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem equilibrium_last_responses
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    LastAliceResponsesNormalized weight nonnegative assessment.strategy :=
  sequentially_rational_last_responses weight nonnegative reward forfeit deposit positive
    rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment
    (continuations_rational_of_rational weight nonnegative assessment
      (LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit) equilibrium.1)

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
      ∀ assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentiallyRational
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
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
    rewardNonnegative (by linarith) (by linarith) marginPositive assessment
    (continuations_rational_of_rational weight nonnegative assessment
      (LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit) rational)

end Vegas.Examples.LateOpeningRuntimeAliceNormalization

namespace Vegas.Examples.LateOpeningRuntimeAliceNormalization
open LateOpeningRuntimeContinuationRationality
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeAliceContinuation
open LateOpeningRuntimeAliceResponseNormalization
open LateOpeningRuntimeAliceFirstRationality
  (sequentially_rational_nongenuine_packet_zero_of_continuation_margin)

theorem sequentially_rational_responses (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (positive : 0 < weight)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (bobDepositPositive : 0 < deposit bob) (aliceDepositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < continuationMargin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : AliceContinuationsRational weight nonnegative assessment
      (LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual) deposit) ∧
      ReceiverContinuationsRational weight nonnegative assessment
        (LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual) deposit)) :
    ResponsesNormalized weight nonnegative assessment.strategy := by
  constructor
  · exact sequentially_rational_last_responses_of_continuation_margin
      weight nonnegative reward forfeit deposit positive rewardNonnegative forfeitPositive
      bobDepositPositive aliceDepositNonnegative marginPositive assessment rational
  · intro site representative decision current
    exact sequentially_rational_nongenuine_packet_zero_of_continuation_margin
      weight nonnegative site representative decision current reward forfeit deposit positive
      rewardNonnegative forfeitPositive bobDepositPositive aliceDepositNonnegative
      marginPositive assessment rational

end Vegas.Examples.LateOpeningRuntimeAliceNormalization

namespace Vegas.Examples.LateOpeningRuntimeAliceNormalization
open LateOpeningRuntimeContinuationRationality
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance
open LateOpeningRuntimeAliceContinuation LateOpeningRuntimeAliceResponseNormalization

theorem exists_service_with_responses_normalized
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardNonnegative : 0 ≤ reward) (largeForfeit : reward < forfeit)
    (aliceCollateral : reward / 2 < deposit alice) (bobDepositPositive : 0 < deposit bob)
    (failureFloor : ℝ) (floorPositive : 0 < failureFloor) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      0 < weight ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      0 < 1 - inclusionProbability weight ∧ 1 - inclusionProbability weight < failureFloor ∧
      ∀ assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment,
        (AliceContinuationsRational weight nonnegative assessment
          (LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual) deposit) ∧
          ReceiverContinuationsRational weight nonnegative assessment
            (LateOpeningRuntimeGame.payoff reward forfeit
              (fun actual => PMF.pure actual) deposit)) →
          ResponsesNormalized weight nonnegative assessment.strategy := by
  have totalPositive : 0 < forfeit + deposit alice + reward / 2 := by linarith
  have gapPositive : 0 < min (forfeit - reward) (deposit alice - reward / 2) := by
    exact lt_min (sub_pos.mpr largeForfeit) (sub_pos.mpr aliceCollateral)
  let floor := min failureFloor
    (min (forfeit - reward) (deposit alice - reward / 2) / (forfeit + deposit alice + reward / 2))
  have positiveFloor : 0 < floor := lt_min floorPositive (div_pos gapPositive totalPositive)
  obtain ⟨weight, nonnegative, positive, contract, blind, receipts⟩ :=
    LateOpeningRuntimeTerminalReceipt.exists_joint_service_with_exact_failure floor positiveFloor
  obtain ⟨_, _, _, close⟩ := receipts false 0 0
  rw [LateOpeningRuntimeTerminalReceipt.terminal_receipt_probability] at close
  have scaled := mul_lt_mul_of_pos_right
    (close.trans_le (min_le_right failureFloor _)) totalPositive
  rw [div_mul_cancel₀ _ (ne_of_gt totalPositive)] at scaled
  have marginPositive : 0 < continuationMargin
      weight reward forfeit deposit := by
    unfold continuationMargin
    linarith
  refine ⟨weight, nonnegative, positive, contract, blind,
    sub_pos.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1),
    close.trans_le (min_le_left failureFloor _), ?_⟩
  intro assessment rational
  exact sequentially_rational_responses weight nonnegative reward forfeit deposit positive
    rewardNonnegative (by linarith) bobDepositPositive (by linarith)
    marginPositive assessment rational

end Vegas.Examples.LateOpeningRuntimeAliceNormalization
