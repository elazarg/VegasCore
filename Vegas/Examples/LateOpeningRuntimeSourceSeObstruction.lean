/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSourceForfeiture
import Vegas.Examples.LateOpeningRuntimeUniformSeObstruction

/-! # A forfeiture source equilibrium without a native SE realization

Fix the reward, publication forfeit and audit deposits first. The complete
source interface admits one equilibrium with the successful Safe joint law,
including its permitted failed bindings and withheld publications. For every
positive requested failure bound, one admissible native service has smaller
strictly positive canonical late-opening failure and has native equilibria,
but none reproduces that selected source terminal-store and payoff law.

The source equilibrium is chosen before the requested bound and the builder.
The builder is chosen before all native equilibria. The native comparison
uses the full authentic audit record and realized net settlement.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSourceSeObstruction

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimePreservingLaw

/-- One fixed full-forfeiture source equilibrium fails to have a native SE
realization for admissible services with arbitrarily small late failure. -/
theorem exists_source_equilibrium_with_uniform_service_obstruction
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardPositive : 0 < reward) (largeForfeit : reward < forfeit)
    (coversBob : 1 ≤ forfeit) (aliceCollateral : reward < deposit alice)
    (bobCollateral : 1 < deposit bob) :
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
          (∃ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
            assessment.IsSequentialEquilibrium
              (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler
                  weight nonnegative)).decisionInformationAntichain
              (rawMenu.bounded initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
              (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
                (fun actual => PMF.pure actual) deposit history.state who)) ∧
          ∀ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
            assessment.IsSequentialEquilibrium
              (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler
                  weight nonnegative)).decisionInformationAntichain
              (rawMenu.bounded initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
              (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
                (fun actual => PMF.pure actual) deposit history.state who) →
            nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
              deposit assessment.strategy ≠ forfeitingTerminalLaw reward forfeit source.strategy :=
    by
  obtain ⟨source, sourceEquilibrium, sourceLaw⟩ :=
    exists_forfeiting_equilibrium_with_safe_law rewardPositive.le largeForfeit.le coversBob
  refine ⟨source, sourceEquilibrium, sourceLaw, ?_⟩
  intro failureFloor floorPositive
  obtain ⟨weight, nonnegative, positive, contract, blind, failurePositive, close,
    nativeEquilibrium, excludes⟩ :=
    LateOpeningRuntimeUniformSeObstruction.exists_service_with_no_preserving_equilibrium
      reward forfeit deposit rewardPositive largeForfeit aliceCollateral bobCollateral
        failureFloor floorPositive
  refine ⟨weight, nonnegative, positive, contract, blind, failurePositive, close,
    nativeEquilibrium, ?_⟩
  intro assessment equilibrium
  rw [sourceLaw]
  exact excludes assessment equilibrium

end Vegas.Examples.LateOpeningRuntimeSourceSeObstruction
