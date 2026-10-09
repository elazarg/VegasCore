/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceTimingValues

/-! # Native first-opening floor when one successful transcript excludes Safe

The exact original accepted and omitted continuation values give a lower
bound retaining full settlement and sender audit costs. Either successful
transcript assigning no mass to Safe gives a three-quarter-reward floor
conditional on inclusion for each of the first two private labels.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceTimingFloor

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeAliceTimingValues
open LateOpeningRuntimeAliceSuccessfulReduction (safeProbability safeProbability_mem_Icc)
open LateOpeningRuntimeAliceFailureReduction (emptyTrueProbability emptyTrueProbability_mem_Icc)
open LateOpeningRuntimeAliceFailureContinuation (failureValue)
open LateOpeningRuntimeBobBindingDecision (bitGuess)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

private theorem failureValue_nonnegative (rewardNonnegative : 0 ≤ reward)
    (label : Fin 3) (answer : Answer) : 0 ≤ failureValue reward label answer := by
  unfold failureValue
  split_ifs
  · exact rewardNonnegative
  · exact le_refl _

private theorem emptyValue_nonnegative (rewardNonnegative : 0 ≤ reward)
    (players : Player → app.Policy) (label : Fin 3) : 0 ≤ emptyValue reward players label := by
  have probability := emptyTrueProbability_mem_Icc players
  unfold emptyValue
  split_ifs
  · exact mul_nonneg probability.1 rewardNonnegative
  · exact mul_nonneg (sub_nonneg.mpr probability.2) rewardNonnegative
  · exact le_refl _

variable (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
  (forfeitPositive : 0 < forfeit) (aliceDepositNonnegative : 0 ≤ deposit alice)
  (bobDepositPositive : 0 < deposit bob)
  (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
  (rational : assessment.IsSequentiallyRational
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
      (fun actual => PMF.pure actual) deposit history.state who))
  (players : Player → app.Policy)
  (bobPolicy : players bob =
    LateOpeningRuntimeFirstRetryComparison.players weight nonnegative assessment.strategy bob)

include positive rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive
  rational bobPolicy in
theorem settlement_value_lower (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (possible : slot = 0 ∨ seen = false) :
    inclusionProbability weight * successValue reward players bit label seen -
        (1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      settlementValue weight nonnegative reward forfeit deposit players bit label slot seen := by
  have failureNonnegative : 0 ≤ 1 - inclusionProbability weight :=
    (sub_pos.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1)).le
  have knownNonnegative := failureValue_nonnegative reward rewardNonnegative label (bitGuess bit)
  have emptyNonnegative := emptyValue_nonnegative reward rewardNonnegative players label
  cases seen
  · rw [unseen_settlement_value weight nonnegative reward forfeit deposit positive
      rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive assessment
        rational players bobPolicy bit label slot]
    nlinarith [mul_nonneg failureNonnegative (add_nonneg knownNonnegative emptyNonnegative)]
  · have first : slot = 0 := possible.resolve_right (by decide)
    subst slot
    rw [first_seen_settlement_value weight nonnegative reward forfeit deposit positive
      rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive assessment
        rational players bobPolicy bit label]
    nlinarith [mul_nonneg failureNonnegative knownNonnegative]

include positive rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive
  rational bobPolicy in
/-- This is the original complete settlement value, including positive failure
probability and the actual sender audit deposit; no loss term is discarded. -/
theorem first_value_lower_of_safe_zero (bit : Bool) (label : Fin 3) (lowLabel : label.val < 2)
    (oneZero : safeProbability players bit true = 0 ∨ safeProbability players bit false = 0) :
    3 * inclusionProbability weight * reward / 4 -
        (1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      firstTimingValue weight nonnegative reward forfeit deposit players bit label := by
  have seen := settlement_value_lower weight nonnegative reward forfeit deposit positive
    rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive assessment
      rational players bobPolicy bit label 0 true (Or.inl rfl)
  have unseen := settlement_value_lower weight nonnegative reward forfeit deposit positive
    rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive assessment
      rational players bobPolicy bit label 0 false (Or.inl rfl)
  have successFloor := LateOpeningRuntimeTimingPreference.successful_first_floor reward
    (safeProbability players bit true) (safeProbability players bit false) rewardNonnegative
      (safeProbability_mem_Icc players bit true).2 (safeProbability_mem_Icc players bit false).2
        oneZero
  have inclusionNonnegative := MessageNetwork.inclusionMass_nonnegative weight nonnegative 1
  have scaled := mul_le_mul_of_nonneg_left successFloor inclusionNonnegative
  unfold firstTimingValue
  simp only [successValue, ite_eq_left lowLabel] at seen unseen
  nlinarith

end Vegas.Examples.LateOpeningRuntimeAliceTimingFloor
