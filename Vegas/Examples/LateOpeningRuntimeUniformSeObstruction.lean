/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSeObstruction
import Vegas.Examples.LateOpeningRuntimeAliceNormalization
import Vegas.Examples.LateOpeningRuntimeEquilibrium

/-! # Fixed collateral before a native service preventing SE preservation

For every fixed positive reward and sufficiently large fixed publication
forfeit and audit deposits, one finite public chance builder satisfies the
unchanged native service requirements, admits native sequential equilibria,
and prevents all of them from realizing the source Safe joint terminal law.
Its canonical late-opening failure can be made arbitrarily small and remains
strictly positive. The builder is exogenous and common knowledge.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeUniformSeObstruction

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimePreservingLaw

/-- The order is fixed collateral, then one admissible finite service, then
every native equilibrium. No equilibrium-dependent builder is selected. -/
theorem exists_service_with_no_preserving_equilibrium
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardPositive : 0 < reward) (largeForfeit : reward < forfeit)
    (aliceCollateral : reward < deposit alice) (bobCollateral : 1 < deposit bob)
    (failureFloor : ℝ) (floorPositive : 0 < failureFloor) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      0 < weight ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      0 < 1 - inclusionProbability weight ∧
      1 - inclusionProbability weight < failureFloor ∧
      (∃ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
            (fun actual => PMF.pure actual) deposit history.state who)) ∧
      ∀ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
            (fun actual => PMF.pure actual) deposit history.state who) →
        nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
          deposit assessment.strategy ≠ safeTerminalLaw reward := by
  have forfeitPositive : 0 < forfeit := rewardPositive.trans largeForfeit
  have alicePositive : 0 < deposit alice := rewardPositive.trans aliceCollateral
  have lossPositive : 0 < forfeit + deposit alice := add_pos forfeitPositive alicePositive
  have denominator : 0 < 3 * reward + 4 * (forfeit + deposit alice) := by positivity
  let small := min failureFloor (reward / (3 * reward + 4 * (forfeit + deposit alice)))
  have smallPositive : 0 < small := lt_min floorPositive (div_pos rewardPositive denominator)
  obtain ⟨weight, nonnegative, positive, contract, blind, failurePositive, close,
    openingMargin, _⟩ :=
    LateOpeningRuntimeAliceNormalization.exists_service_with_last_responses_normalized
      reward forfeit deposit rewardPositive.le largeForfeit aliceCollateral small smallPositive
  have retryMargin : 0 < LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit :=
    by
    unfold LateOpeningRuntimeAliceRationality.margin
    unfold LateOpeningRuntimeAliceOpeningRationality.margin at openingMargin
    linarith [min_le_right forfeit (deposit alice)]
  have profitable : reward / 2 < 3 * inclusionProbability weight * reward / 4 -
      (1 - inclusionProbability weight) * (forfeit + deposit alice) := by
    have profitable := LateOpeningRuntimeTimingPreference.first_floor_exceeds_safe reward
      (1 - inclusionProbability weight) (forfeit + deposit alice) rewardPositive lossPositive.le
        (close.trans_le (min_le_right failureFloor _))
    convert profitable using 1
    ring
  refine ⟨weight, nonnegative, positive, contract, blind, failurePositive,
    close.trans_le (min_le_left failureFloor _), ?_, ?_⟩
  · exact LateOpeningRuntimeEquilibrium.exists_sequential_equilibrium weight nonnegative
      reward forfeit (fun actual => PMF.pure actual) deposit
  · intro assessment equilibrium
    exact LateOpeningRuntimeSeObstruction.equilibrium_terminal_law_ne_safe weight nonnegative
      reward forfeit deposit positive rewardPositive forfeitPositive alicePositive.le bobCollateral
        retryMargin openingMargin profitable assessment equilibrium

end Vegas.Examples.LateOpeningRuntimeUniformSeObstruction
