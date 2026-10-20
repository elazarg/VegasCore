/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPublicClassConstancy

/-! # Exact full-information source class and reach contracts -/

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
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (wellFormed : setup.WellFormed) (focal : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (leftTrace : setup.proposalRecoveryProtocol.Trace leftState)
    (rightTrace : setup.proposalRecoveryProtocol.Trace rightState)
    (same : setup.proposalRecoveryModel.infoOf focal leftTrace =
      setup.proposalRecoveryModel.infoOf focal rightTrace)
    (leftGood : ∀ owner, owner ≠ focal →
      ¬ setup.GeneratedPreparationHistory owner ⟨leftState, leftTrace⟩)
    (rightGood : ∀ owner, owner ≠ focal →
      ¬ setup.GeneratedPreparationHistory owner ⟨rightState, rightTrace⟩) :
    (setup.proposalRecoveryForeignProducts values omission bad delivery focal leftTrace).1 =
      (setup.proposalRecoveryForeignProducts values omission bad delivery focal rightTrace).1 := by
  exact setup.proposalRecovery_foreign_class_eq_of_information values omission bad delivery
    omissionPositive omissionBelow badBelow deliveryPositive deliveryBelow wellFormed focal
      leftTrace rightTrace same leftGood rightGood

example
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (wellFormed : setup.WellFormed) (focal : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (good : ∀ owner, owner ≠ focal →
      ¬ setup.GeneratedPreparationHistory owner ⟨state, trace⟩) :
    0 < (setup.proposalRecoveryForeignProducts values omission bad delivery focal trace).1 := by
  exact setup.proposalRecovery_foreign_class_pos_of_good values omission bad delivery
    omissionPositive omissionBelow badBelow deliveryPositive deliveryBelow wellFormed focal
      trace good

example
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (wellFormed : setup.WellFormed) (focal : Player) :
    ∃ coefficient : setup.proposalRecoveryModel.InfoState focal → ℝ≥0∞,
      (∀ information, 0 < coefficient information ∧ coefficient information ≠ ⊤) ∧
      (∀ history : setup.proposalRecoveryProtocol.History,
        (∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner history) →
        coefficient (setup.proposalRecoveryModel.infoOf focal history.trace) =
          (setup.proposalRecoveryForeignProducts values omission bad delivery focal
            history.trace).1) ∧
      ∀ history : setup.proposalRecoveryProtocol.History,
        (∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner history) →
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
                coefficient (setup.proposalRecoveryModel.infoOf focal history.trace) *
                  factors.2.1 * factors.2.2 := by
  exact setup.proposalRecovery_foreign_information_factor values omission bad delivery
    omissionPositive omissionBelow badBelow deliveryPositive deliveryBelow wellFormed focal

end Vegas.SourceProgram.Setup
