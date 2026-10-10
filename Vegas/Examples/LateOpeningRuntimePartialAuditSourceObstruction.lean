/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSourceForfeiture
import Vegas.Examples.LateOpeningRuntimePartialAudit

/-! # A fixed source equilibrium excluded under partial sender auditing

The source equilibrium, audit sampling probability and deposits are fixed before
selecting an arbitrarily reliable native service. The unchanged full raw native
game has sequential equilibria, none with this source joint outcome and realized
settlement law. Receiver evidence and public binding omissions are fully audited.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimePartialAuditSourceObstruction

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimePreservingLaw

/-- Partial sender auditing excludes one fixed source equilibrium for
admissible native services with arbitrarily small late-opening failure. -/
theorem exists_source_equilibrium_with_partial_audit_obstruction
    (probability : ℝ) (samplingPositive : 0 < probability) (bounded : probability ≤ 1)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardPositive : 0 < reward) (largeForfeit : reward < forfeit)
    (coversBob : 1 ≤ forfeit) (aliceCollateral : reward < probability * deposit alice)
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
                (LateOpeningRuntimePartialAudit.sample probability samplingPositive.le bounded)
                  deposit history.state who)) ∧
          ∀ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
            assessment.IsSequentialEquilibrium
              (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler
                  weight nonnegative)).decisionInformationAntichain
              (rawMenu.bounded initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
              (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
                (LateOpeningRuntimePartialAudit.sample probability samplingPositive.le bounded)
                  deposit history.state who) →
            nativeTerminalLaw weight nonnegative reward forfeit
              (LateOpeningRuntimePartialAudit.sample probability samplingPositive.le bounded)
              deposit assessment.strategy ≠ forfeitingTerminalLaw reward forfeit source.strategy :=
    by
  obtain ⟨source, sourceEquilibrium, sourceLaw⟩ :=
    exists_forfeiting_equilibrium_with_safe_law rewardPositive.le largeForfeit.le coversBob
  refine ⟨source, sourceEquilibrium, sourceLaw, ?_⟩
  intro failureFloor floorPositive
  obtain ⟨weight, nonnegative, positive, contract, blind, failurePositive, close,
    nativeEquilibrium, excludes⟩ :=
    LateOpeningRuntimePartialAudit.exists_service_with_no_preserving_equilibrium
      probability samplingPositive bounded reward forfeit deposit rewardPositive largeForfeit
        aliceCollateral bobCollateral failureFloor floorPositive
  refine ⟨weight, nonnegative, positive, contract, blind, failurePositive, close,
    nativeEquilibrium, ?_⟩
  intro assessment equilibrium
  rw [sourceLaw]
  exact excludes assessment equilibrium

end Vegas.Examples.LateOpeningRuntimePartialAuditSourceObstruction
