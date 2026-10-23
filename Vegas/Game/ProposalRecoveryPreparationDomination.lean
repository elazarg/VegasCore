/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPools
import GameTheory.Math.Probability.Domination

/-! # Source ordinary domination before choosing unusable-preparation noise

The surrogate keeps positive omission and failed-disclosure labels. Only the
bad preparation component is zero; there is no menu-support totalization.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem preparation_map_lower {A B : Type*} (source target : PMF A)
    (factor : ℝ) (lower : ∀ value, factor * (source value).toReal ≤ (target value).toReal)
    (encode : A → B) (value : B) :
    factor * ((source.map encode) value).toReal ≤ ((target.map encode) value).toReal := by
  simpa only [pmf_bind_pure_eq_map] using
    prob_bind_ge_mul source target factor lower (fun item => PMF.pure (encode item)) value

/-- The semantic source law retains timing omissions while removing only
unusable preparation. The factor is independent of all optimized weights. -/
theorem commitRecoveryValueTremble_preparation_domination (who : Player)
    (information : setup.commitRecoveryModel.InfoState who)
    (omission bad : Set.Icc (0 : ℝ) 1)
    (source target : PMF (setup.CommitRecoveryValueChoice who information))
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (domain : ∀ value, floor * (source value).toReal ≤ (target value).toReal)
    (choice : setup.commitRecoveryModel.Choice who information) :
    ((1 - bad.val) * floor) *
        (setup.commitRecoveryValueTremble who information omission.val omission.property.1
          omission.property.2 0 le_rfl zero_le_one source choice).toReal ≤
      (setup.commitRecoveryValueTremble who information omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 target choice).toReal := by
  have bounded : (1 - bad.val) * floor ≤ 1 :=
    (mul_le_of_le_one_left floorNonnegative (by linarith [bad.property.1])).trans floorBounded
  have mapped := preparation_map_lower source target floor domain Subtype.val choice
  have ordinary : ((1 - bad.val) * floor) * ((source.map Subtype.val) choice).toReal ≤
      ((if information.1.1.1.elim false (ProtocolView.atCommit who setup.program) then
        mix bad.val bad.property.1 bad.property.2
          (PMF.pure (setup.commitRecoveryFailureChoice who information false))
          (target.map Subtype.val)
      else target.map Subtype.val) choice).toReal := by
    split
    · rw [mix_apply_toReal]
      have weighted := mul_le_mul_of_nonneg_left mapped (sub_nonneg.mpr bad.property.2)
      have extra : 0 ≤ bad.val * ((PMF.pure
          (setup.commitRecoveryFailureChoice who information false)) choice).toReal :=
        mul_nonneg bad.property.1 ENNReal.toReal_nonneg
      nlinarith
    · exact (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left floorNonnegative (by linarith [bad.property.1]))
        ENNReal.toReal_nonneg).trans mapped
  simp only [commitRecoveryValueTremble, mix_zero, ite_self]
  rw [mix_apply_toReal, mix_apply_toReal]
  have missing : ((1 - bad.val) * floor) *
      ((PMF.pure (setup.commitRecoveryFailureChoice who information true)) choice).toReal ≤
      ((PMF.pure (setup.commitRecoveryFailureChoice who information true)) choice).toReal :=
    mul_le_of_le_one_left ENNReal.toReal_nonneg bounded
  have left := mul_le_mul_of_nonneg_left missing omission.property.1
  have right := mul_le_mul_of_nonneg_left ordinary (sub_nonneg.mpr omission.property.2)
  nlinarith

/-- Proposal-label probabilities are unchanged on both sides, including the
positive failed-disclosure branch and its no-proposal complement. -/
theorem proposalRecoveryComponentTrembledLaw_preparation_domination (who : Player)
    (key : setup.ProposalRecoveryComponent who) (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (source target : PMF (setup.CommitRecoveryValueChoice who key.1))
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (domain : ∀ value, floor * (source value).toReal ≤ (target value).toReal)
    (choice : setup.ProposalRecoveryComponentChoice who key) :
    ((1 - bad.val) * floor) *
        (setup.proposalRecoveryComponentTrembledLaw who key omission.val omission.property.1
          omission.property.2 0 le_rfl zero_le_one delivery.val delivery.property.1
          delivery.property.2 source choice).toReal ≤
      (setup.proposalRecoveryComponentTrembledLaw who key omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val delivery.property.1
        delivery.property.2 target choice).toReal := by
  exact prob_bind_ge_mul
    (setup.commitRecoveryValueTremble who key.1 omission.val omission.property.1
      omission.property.2 0 le_rfl zero_le_one source)
    (setup.commitRecoveryValueTremble who key.1 omission.val omission.property.1
      omission.property.2 bad.val bad.property.1 bad.property.2 target)
    ((1 - bad.val) * floor)
    (setup.commitRecoveryValueTremble_preparation_domination who key.1 omission bad source target
      floor floorNonnegative floorBounded domain)
    (fun semantic =>
      (mix delivery.val delivery.property.1 delivery.property.2 (PMF.pure true)
        (PMF.pure false)).map fun flag =>
          setup.proposalRecoveryComponentLabelChoice who key flag semantic) choice

/-- Actual full-information source policies inherit the same pointwise
comparison through their literal legal-choice equivalence. -/
theorem proposalRecoveryNormalizedTrembledProfile_preparation_domination
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (source target : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (domain : ∀ who key value, floor * (source who key value).toReal ≤
      (target who key value).toReal)
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (choice : setup.proposalRecoveryModel.Choice who information) :
    ((1 - bad.val) * floor) *
        (setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
          omission.property.2 0 le_rfl zero_le_one delivery.val delivery.property.1
          delivery.property.2 source who information choice).toReal ≤
      (setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val delivery.property.1
        delivery.property.2 target who information choice).toReal := by
  exact preparation_map_lower _ _ ((1 - bad.val) * floor)
    (setup.proposalRecoveryComponentTrembledLaw_preparation_domination who
      (setup.proposalRecoveryQuery who information) omission bad delivery
      (source who (setup.proposalRecoveryQuery who information))
      (target who (setup.proposalRecoveryQuery who information)) floor floorNonnegative floorBounded
      (domain who (setup.proposalRecoveryQuery who information)))
    (setup.proposalRecoveryComponentChoice who information).symm choice

end Vegas.SourceProgram.Setup
