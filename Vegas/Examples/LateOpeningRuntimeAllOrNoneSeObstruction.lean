/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAllOrNoneAlice
import Vegas.Examples.LateOpeningRuntimeAllOrNoneEarlyBob
import Vegas.Examples.LateOpeningRuntimeAllOrNoneRationality
import Vegas.Examples.LateOpeningRuntimeAllOrNonePreservingSettlement
import Vegas.Examples.LateOpeningRuntimeSeObstruction
import Vegas.Examples.LateOpeningRuntimeAliceNormalization
import Vegas.Examples.LateOpeningRuntimeEquilibrium
import Vegas.Examples.LateOpeningRuntimeSourceForfeiture

/-! # Sequential-equilibrium obstruction with all-or-none traffic sampling

The sampler changes observed signed traffic while public omissions remain
deterministic. Actual player-specific rationality and the original consistency
sequence yield the obstruction; no global equilibrium equivalence is used.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAllOrNoneSeObstruction

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimePreservingLaw LateOpeningRuntimeContinuationRationality
  LateOpeningRuntimeAliceResponseNormalization LateOpeningRuntimeAllOrNoneTrafficAudit

theorem equilibrium_terminal_law_ne_safe
    (probability : ℝ) (samplingPositive : 0 < probability) (bounded : probability ≤ 1)
    (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (positive : 0 < weight) (rewardPositive : 0 < reward) (forfeitPositive : 0 < forfeit)
    (aliceDepositNonnegative : 0 ≤ probability * deposit alice)
    (bobCollateral : 1 < probability * deposit bob)
    (profitable : reward / 2 < 3 * inclusionProbability weight * reward / 4 -
      (1 - inclusionProbability weight) * (forfeit + probability * deposit alice))
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (normalized : ResponsesNormalized weight nonnegative assessment.strategy)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability samplingPositive.le bounded) deposit history.state who)) :
    nativeTerminalLaw weight nonnegative reward forfeit
      (sample probability samplingPositive.le bounded) deposit assessment.strategy ≠
        safeTerminalLaw reward := by
  intro same
  have bobDepositNonnegative : 0 ≤ deposit bob := by
    by_contra negative
    have upper := mul_nonpos_of_nonneg_of_nonpos samplingPositive.le
      (le_of_lt (lt_of_not_ge negative))
    linarith
  have sampledContinuations := continuations_rational_of_rational weight nonnegative assessment
    (LateOpeningRuntimeGame.payoff reward forfeit
      (sample probability samplingPositive.le bounded) deposit) equilibrium.1
  have aliceRational := LateOpeningRuntimeAllOrNoneAlice.rational_alice probability
    samplingPositive.le bounded weight nonnegative reward forfeit deposit assessment equilibrium.1
  have receiverRational := LateOpeningRuntimeAllOrNoneRationality.receiver_continuations_rational
    probability samplingPositive.le bounded weight nonnegative reward forfeit deposit
      forfeitPositive.le bobDepositNonnegative assessment sampledContinuations.2
  have silent := LateOpeningRuntimeAllOrNoneEarlyBob.sequentially_rational_responses_silent
    probability samplingPositive.le bounded weight nonnegative reward forfeit deposit
      forfeitPositive.le bobCollateral assessment equilibrium.1
  have fullSame := LateOpeningRuntimeAllOrNonePreservingSettlement.preserving_implies_full
    probability samplingPositive bounded weight nonnegative reward forfeit deposit
      assessment.strategy same
  exact LateOpeningRuntimeSeObstruction.consistent_rational_terminal_law_ne_safe weight
    nonnegative reward forfeit (fun owner => probability * deposit owner) positive rewardPositive
      forfeitPositive aliceDepositNonnegative bobCollateral profitable assessment normalized
        ⟨aliceRational, receiverRational⟩ equilibrium.2 silent fullSame

/-- Sampling and both deposits are fixed before the service builder and before
every native sampled-audit equilibrium. The late failure remains positive. -/
theorem exists_service_with_no_preserving_equilibrium
    (probability : ℝ) (samplingPositive : 0 < probability) (bounded : probability ≤ 1)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardPositive : 0 < reward) (largeForfeit : reward < forfeit)
    (aliceCollateral : reward / 2 < probability * deposit alice)
    (bobCollateral : 1 < probability * deposit bob)
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
      (∃ assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
            (sample probability samplingPositive.le bounded) deposit history.state who)) ∧
      ∀ assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
            (sample probability samplingPositive.le bounded) deposit history.state who) →
        nativeTerminalLaw weight nonnegative reward forfeit
          (sample probability samplingPositive.le bounded) deposit assessment.strategy ≠
            safeTerminalLaw reward := by
  let scaled := fun owner => probability * deposit owner
  have forfeitPositive : 0 < forfeit := rewardPositive.trans largeForfeit
  have alicePositive : 0 < scaled alice := lt_trans (by linarith) aliceCollateral
  have bobDepositNonnegative : 0 ≤ deposit bob := by
    by_contra negative
    have upper := mul_nonpos_of_nonneg_of_nonpos samplingPositive.le
      (le_of_lt (lt_of_not_ge negative))
    linarith
  have lossPositive : 0 < forfeit + scaled alice := add_pos forfeitPositive alicePositive
  have denominator : 0 < 3 * reward + 4 * (forfeit + scaled alice) := by positivity
  let small := min failureFloor (reward / (3 * reward + 4 * (forfeit + scaled alice)))
  have smallPositive : 0 < small := lt_min floorPositive (div_pos rewardPositive denominator)
  obtain ⟨weight, nonnegative, positive, contract, blind, failurePositive, close, normalized⟩ :=
    LateOpeningRuntimeAliceNormalization.exists_service_with_responses_normalized
      reward forfeit scaled rewardPositive.le largeForfeit aliceCollateral
        (lt_trans zero_lt_one bobCollateral) small smallPositive
  have profitable : reward / 2 < 3 * inclusionProbability weight * reward / 4 -
      (1 - inclusionProbability weight) * (forfeit + scaled alice) := by
    have lower := LateOpeningRuntimeTimingPreference.first_floor_exceeds_safe reward
      (1 - inclusionProbability weight) (forfeit + scaled alice) rewardPositive lossPositive.le
        (close.trans_le (min_le_right failureFloor _))
    convert lower using 1
    ring
  refine ⟨weight, nonnegative, positive, contract, blind, failurePositive,
    close.trans_le (min_le_left failureFloor _), ?_, ?_⟩
  · exact LateOpeningRuntimeEquilibrium.exists_sequential_equilibrium weight nonnegative
      reward forfeit (sample probability samplingPositive.le bounded) deposit
  · intro assessment equilibrium
    have sampledContinuations := continuations_rational_of_rational weight nonnegative assessment
      (LateOpeningRuntimeGame.payoff reward forfeit
        (sample probability samplingPositive.le bounded) deposit) equilibrium.1
    have aliceRational := LateOpeningRuntimeAllOrNoneAlice.rational_alice probability
      samplingPositive.le bounded weight nonnegative reward forfeit deposit assessment equilibrium.1
    have receiverRational :=
      LateOpeningRuntimeAllOrNoneRationality.receiver_continuations_rational probability
        samplingPositive.le bounded weight nonnegative reward forfeit deposit forfeitPositive.le
          bobDepositNonnegative assessment sampledContinuations.2
    exact equilibrium_terminal_law_ne_safe probability samplingPositive bounded weight nonnegative
      reward forfeit deposit positive rewardPositive forfeitPositive alicePositive.le bobCollateral
        profitable assessment (normalized assessment ⟨aliceRational, receiverRational⟩) equilibrium

/-- One fixed full-forfeiture source equilibrium fails to have a native SE
realization for admissible services with arbitrarily small late failure. -/
theorem exists_source_equilibrium_with_uniform_service_obstruction
    (probability : ℝ) (samplingPositive : 0 < probability) (bounded : probability ≤ 1)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardPositive : 0 < reward) (largeForfeit : reward < forfeit)
    (coversBob : 1 ≤ forfeit) (aliceCollateral : reward / 2 < probability * deposit alice)
    (bobCollateral : 1 < probability * deposit bob) :
    ∃ source : forfeitingModel.BehavioralAssessment,
      source.IsSequentialEquilibrium
        (setup.decision_antichain (CommitmentInterface.forfeiture setup.program))
        forfeiting_bounded.wellFoundedHistories (forfeitingPayoff reward forfeit) ∧
      forfeitingTerminalLaw reward forfeit source.strategy = safeTerminalLaw reward ∧
      ∀ failureFloor : ℝ, 0 < failureFloor →
        ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
          0 < weight ∧
          LateOpeningRuntimeService.runtime.AsyncContract leaks initial
            LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) delay bound ∧
          LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
            (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
          0 < 1 - inclusionProbability weight ∧
          1 - inclusionProbability weight < failureFloor ∧
          (∃ assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment,
            assessment.IsSequentialEquilibrium
              (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler
                  weight nonnegative)).decisionInformationAntichain
              (rawMenu.bounded initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
              (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
                (sample probability samplingPositive.le bounded) deposit history.state who)) ∧
          ∀ assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment,
            assessment.IsSequentialEquilibrium
              (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler
                  weight nonnegative)).decisionInformationAntichain
              (rawMenu.bounded initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
              (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
                (sample probability samplingPositive.le bounded) deposit history.state who) →
            nativeTerminalLaw weight nonnegative reward forfeit
              (sample probability samplingPositive.le bounded) deposit assessment.strategy ≠
                forfeitingTerminalLaw reward forfeit source.strategy :=
    by
  obtain ⟨source, sourceEquilibrium, sourceLaw⟩ :=
    exists_forfeiting_equilibrium_with_safe_law rewardPositive.le largeForfeit.le coversBob
  refine ⟨source, sourceEquilibrium, sourceLaw, ?_⟩
  intro failureFloor floorPositive
  obtain ⟨weight, nonnegative, positive, contract, blind, failurePositive, close,
    nativeEquilibrium, excludes⟩ :=
    exists_service_with_no_preserving_equilibrium probability samplingPositive bounded
      reward forfeit deposit rewardPositive largeForfeit aliceCollateral bobCollateral
        failureFloor floorPositive
  refine ⟨weight, nonnegative, positive, contract, blind, failurePositive, close,
    nativeEquilibrium, ?_⟩
  intro assessment equilibrium
  rw [sourceLaw]
  exact excludes assessment equilibrium


end Vegas.Examples.LateOpeningRuntimeAllOrNoneSeObstruction
