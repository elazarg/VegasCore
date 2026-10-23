/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPublicClassFactorization

/-! # Exact whole-history source reach contracts -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

example
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (history : setup.proposalRecoveryProtocol.History) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 values
    let factors := setup.proposalRecoveryForeignProducts values omission bad delivery focal
      history.trace
    (setup.proposalRecoveryModel.historyReachWeight profile history).toReal =
      history.trace.transitionMass *
        setup.proposalRecoveryModel.ownPlayReachProbability (profile focal)
          (setup.proposalRecoveryModel.ownPlay focal history.trace) *
            factors.1.toReal * factors.2.1.toReal * factors.2.2.toReal := by
  exact setup.proposalRecovery_historyReach_foreign_products values omission bad delivery
    focal history

example
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (history : setup.proposalRecoveryProtocol.History) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 values
    let factors := setup.proposalRecoveryForeignProducts values omission bad delivery focal
      history.trace
    setup.proposalRecoveryModel.historyReachWeight profile history =
      ENNReal.ofReal history.trace.transitionMass *
        ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability (profile focal)
          (setup.proposalRecoveryModel.ownPlay focal history.trace)) *
            factors.1 * factors.2.1 * factors.2.2 := by
  exact setup.proposalRecovery_historyReachWeight_foreign_products values omission bad delivery
    focal history

end Vegas.SourceProgram.Setup
