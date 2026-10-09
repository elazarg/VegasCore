/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeFirstOpeningPayoff
import Vegas.Examples.LateOpeningRuntimeSecondOpeningPayoff
import Vegas.Examples.LateOpeningRuntimeAliceSuccessfulReduction
import Vegas.Examples.LateOpeningRuntimeTimingPreference

/-! # Actual sender values at the two late opening times

The acceptance and omission branches retain the original raw receiver
strategy. Its two successful Safe probabilities and its one empty-failure
guess probability determine the sender's complete canonical settlement
values. Publication forfeits and audit costs occur only on omission.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceTimingValues

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeSettlementContinuation
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeFirstRetryComparison
open LateOpeningRuntimeAliceSuccessfulReduction (safeProbability)
open LateOpeningRuntimeAliceFailureReduction (emptyTrueProbability)
open LateOpeningRuntimeAliceFailureContinuation (failureValue)
open LateOpeningRuntimeBobBindingDecision (bitGuess)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

private theorem utility_payoff : aliceUtility reward forfeit deposit =
    fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final) alice := rfl

def settlementValue (players : Player → app.Policy) (bit : Bool) (label : Fin 3)
    (slot : Fin 2) (seen : Bool) : ℝ :=
  expect (settlementCompletion weight nonnegative players (beforeLottery bit label slot seen))
    (aliceUtility reward forfeit deposit)

def successValue (players : Player → app.Policy) (bit : Bool) (label : Fin 3) (seen : Bool) : ℝ :=
  if label.val < 2 then reward * (1 - safeProbability players bit seen / 2)
    else reward * safeProbability players bit seen / 2

def emptyValue (players : Player → app.Policy) (label : Fin 3) : ℝ :=
  if label.val = 0 then emptyTrueProbability players * reward
    else if label.val = 1 then (1 - emptyTrueProbability players) * reward else 0

def firstTimingValue (players : Player → app.Policy) (bit : Bool) (label : Fin 3) : ℝ :=
  (settlementValue weight nonnegative reward forfeit deposit players bit label 0 true +
    settlementValue weight nonnegative reward forfeit deposit players bit label 0 false) / 2

def secondTimingValue (players : Player → app.Policy) (bit : Bool) (label : Fin 3) : ℝ :=
  settlementValue weight nonnegative reward forfeit deposit players bit label 1 false

def successfulPull (players : Player → app.Policy) (bit : Bool) : ℝ :=
  inclusionProbability weight * reward *
    (safeProbability players bit false - safeProbability players bit true) / 4

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
theorem first_seen_settlement_value (bit : Bool) (label : Fin 3) :
    settlementValue weight nonnegative reward forfeit deposit players bit label 0 true =
      inclusionProbability weight * successValue reward players bit label true +
        (1 - inclusionProbability weight) *
          (failureValue reward label (bitGuess bit) - forfeit - deposit alice) := by
  have integrable (law : PMF app.Execution) :
      PayoffIntegrable law (aliceUtility reward forfeit deposit) :=
    aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit aliceDepositNonnegative law
  unfold settlementValue
  rw [canonical_completion_law,
    expect_mix _ _ _ _ _ _ (integrable _) (integrable _),
    expect_mix _ _ _ _ _ _ (integrable _) (integrable _)]
  rw [utility_payoff]
  rw [LateOpeningRuntimeAliceSuccessfulReduction.receiver_expected_value_closed weight nonnegative
    positive bit label 0 true (Or.inl rfl) reward forfeit deposit rewardNonnegative forfeitPositive
      aliceDepositNonnegative bobDepositPositive assessment rational players bobPolicy]
  rw [LateOpeningRuntimeAliceFailureReduction.receiver_known_expected_value weight nonnegative
    reward forfeit deposit bit label 0 true true (Or.inl rfl) (Or.inl rfl) rewardNonnegative
      forfeitPositive aliceDepositNonnegative bobDepositPositive assessment rational players
        bobPolicy]
  rw [LateOpeningRuntimeAliceFailureReduction.receiver_known_expected_value weight nonnegative
    reward forfeit deposit bit label 0 true false (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) rewardNonnegative
      forfeitPositive aliceDepositNonnegative bobDepositPositive assessment rational players
        bobPolicy]
  unfold successValue
  ring

include positive rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive
  rational bobPolicy in
theorem unseen_settlement_value (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    settlementValue weight nonnegative reward forfeit deposit players bit label slot false =
      inclusionProbability weight * successValue reward players bit label false +
        (1 - inclusionProbability weight) *
          ((failureValue reward label (bitGuess bit) + emptyValue reward players label) / 2 -
            forfeit - deposit alice) := by
  have integrable (law : PMF app.Execution) :
      PayoffIntegrable law (aliceUtility reward forfeit deposit) :=
    aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit aliceDepositNonnegative law
  unfold settlementValue
  rw [canonical_completion_law,
    expect_mix _ _ _ _ _ _ (integrable _) (integrable _),
    expect_mix _ _ _ _ _ _ (integrable _) (integrable _)]
  rw [utility_payoff]
  rw [LateOpeningRuntimeAliceSuccessfulReduction.receiver_expected_value_closed weight nonnegative
    positive bit label slot false (Or.inr rfl) reward forfeit deposit rewardNonnegative
      forfeitPositive aliceDepositNonnegative bobDepositPositive assessment rational players
        bobPolicy]
  rw [LateOpeningRuntimeAliceFailureReduction.receiver_known_expected_value weight nonnegative
    reward forfeit deposit bit label slot false true (Or.inr rfl) (Or.inl rfl) rewardNonnegative
      forfeitPositive aliceDepositNonnegative bobDepositPositive assessment rational players
        bobPolicy]
  rw [LateOpeningRuntimeAliceFailureReduction.receiver_empty_expected_value_closed
    weight nonnegative
    reward forfeit deposit bit label slot rewardNonnegative forfeitPositive aliceDepositNonnegative
      bobDepositPositive assessment rational players bobPolicy]
  unfold successValue emptyValue
  ring

include positive rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive
  rational bobPolicy in
/-- The two actual canonical timing values differ by one common success term
and opposite bit-knowledge terms for the first two private labels. -/
theorem timing_value_difference (bit : Bool) (label : Fin 3) :
    firstTimingValue weight nonnegative reward forfeit deposit players bit label -
      secondTimingValue weight nonnegative reward forfeit deposit players bit label =
    let success := successfulPull weight reward players bit
    let failure := LateOpeningRuntimeTimingPreference.failurePull
      (1 - inclusionProbability weight) reward (emptyTrueProbability players) bit
    if label.val = 0 then success + failure
      else if label.val = 1 then success - failure else -success := by
  unfold firstTimingValue secondTimingValue
  rw [first_seen_settlement_value weight nonnegative reward forfeit deposit positive
    rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive assessment
      rational players bobPolicy bit label,
    unseen_settlement_value weight nonnegative reward forfeit deposit positive
      rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive assessment
        rational players bobPolicy bit label 0,
    unseen_settlement_value weight nonnegative reward forfeit deposit positive
      rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive assessment
        rational players bobPolicy bit label 1]
  unfold successValue emptyValue successfulPull LateOpeningRuntimeTimingPreference.failurePull
  fin_cases label <;> cases bit <;> norm_num [failureValue, bitGuess] <;> ring

include positive rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive
  rational bobPolicy in
/-- Under the original rational receiver policy, some two private labels of
one original-bit class strictly prefer opposite canonical late sending times. -/
theorem opposite_preferences (rewardPositive : 0 < reward) :
    ∃ bit sender holder,
      secondTimingValue weight nonnegative reward forfeit deposit players bit sender <
        firstTimingValue weight nonnegative reward forfeit deposit players bit sender ∧
      firstTimingValue weight nonnegative reward forfeit deposit players bit holder <
        secondTimingValue weight nonnegative reward forfeit deposit players bit holder := by
  have difference (bit : Bool) (label : Fin 3) := timing_value_difference weight nonnegative
    reward forfeit deposit positive rewardNonnegative forfeitPositive aliceDepositNonnegative
      bobDepositPositive assessment rational players bobPolicy bit label
  apply LateOpeningRuntimeTimingPreference.opposite_timing_preferences
    (firstTimingValue weight nonnegative reward forfeit deposit players)
    (secondTimingValue weight nonnegative reward forfeit deposit players)
    (successfulPull weight reward players) (1 - inclusionProbability weight) reward
    (emptyTrueProbability players)
    (sub_pos.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1)) rewardPositive
  · intro bit
    simpa using difference bit 0
  · intro bit
    simpa using difference bit 1
  · intro bit
    simpa using difference bit 2

include positive rewardNonnegative forfeitPositive aliceDepositNonnegative rational in
/-- Every available genuine first private alias has the canonical first
timing value against the original entire future strategies. -/
theorem first_genuine_response_value
    (marginPositive : 0 < LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit)
    (collateral : 1 < deposit bob) (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (available : (⟨some submission⟩ : app.Action) ∈ rawMenu.actions alice
      ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice))
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) :
    expect (LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        ⟨some submission⟩
          (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative assessment.strategy))
      (aliceUtility reward forfeit deposit) =
    firstTimingValue weight nonnegative reward forfeit deposit
      (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative assessment.strategy)
        bit label := by
  let actual := LateOpeningRuntimeFirstRetryComparison.players weight nonnegative
    assessment.strategy
  have law := LateOpeningRuntimeFirstOpeningPayoff.first_genuine_payoff_law weight nonnegative
    reward forfeit deposit assessment rational positive rewardNonnegative forfeitPositive.le
      aliceDepositNonnegative marginPositive collateral bit label submission available genuine
  have expectations := congrArg (fun distribution : PMF ℝ => expect distribution id) law
  have integrable (seen : Bool) : PayoffIntegrable
      ((settlementCompletion weight nonnegative actual (beforeLottery bit label 0 seen)).map
        (aliceUtility reward forfeit deposit)) id := by
    apply (payoffIntegrable_map_iff _ _ _).mpr
    exact aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit
      aliceDepositNonnegative _
  rw [utility_payoff] at integrable
  rw [expect_mix _ _ _ _ _ _ (integrable true) (integrable false)] at expectations
  have exactValue :
      expect (LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          ⟨some submission⟩ actual) (aliceUtility reward forfeit deposit) =
        (1 / 2 : ℝ) * settlementValue weight nonnegative reward forfeit deposit actual
          bit label 0 true + (1 - 1 / 2) *
            settlementValue weight nonnegative reward forfeit deposit actual bit label 0 false := by
    simpa only [expect_map, Function.comp_def, id_eq, settlementValue, utility_payoff, actual]
      using expectations
  rw [exactValue]
  unfold firstTimingValue
  ring

include positive rewardNonnegative forfeitPositive aliceDepositNonnegative rational in
/-- First late silence keeps the original final opening policy and gives the
canonical second timing value, with all supported private encodings retained. -/
theorem first_silence_response_value
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit) (collateral : 1 < deposit bob)
    (bit : Bool) (label : Fin 3) :
    expect (LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        ⟨none⟩
          (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative assessment.strategy))
      (aliceUtility reward forfeit deposit) =
    secondTimingValue weight nonnegative reward forfeit deposit
      (LateOpeningRuntimeFirstRetryComparison.players weight nonnegative assessment.strategy)
        bit label := by
  have law := LateOpeningRuntimeSecondOpeningPayoff.first_silence_payoff_law weight nonnegative
    reward forfeit deposit positive rewardNonnegative forfeitPositive.le aliceDepositNonnegative
      marginPositive assessment rational collateral bit label
  have expectations := congrArg (fun distribution : PMF ℝ => expect distribution id) law
  simpa only [expect_map, Function.comp_def, id_eq, secondTimingValue, settlementValue,
    utility_payoff]
    using expectations

end Vegas.Examples.LateOpeningRuntimeAliceTimingValues
