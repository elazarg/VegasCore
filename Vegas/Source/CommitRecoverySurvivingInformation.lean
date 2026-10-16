/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryOwnHistory

/-! # Complete source recall of surviving owners after arbitrary foreign exclusions -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A surviving owner's complete observed source transcript determines its
original own play, through all foreign failures and commitment retries. -/
theorem commitRecovery_surviving_ownPlay_eq (who : Player) :
    ∀ {first second : setup.commitRecoveryProtocol.State}
      (firstTrace : setup.commitRecoveryProtocol.Trace first)
      (secondTrace : setup.commitRecoveryProtocol.Trace second)
      (_firstSurvives : who ∉ (setup.commitRecoveryPublic first).1)
      (_secondSurvives : who ∉ (setup.commitRecoveryPublic second).1),
      setup.commitRecoverySignals.infoOf who firstTrace =
          setup.commitRecoverySignals.infoOf who secondTrace →
        setup.commitRecoverySignals.ownPlay who firstTrace =
          setup.commitRecoverySignals.ownPlay who secondTrace
  | _, _, .start, .start, _, _, _ => rfl
  | _, _, .start, .extend prior joint legal supported, _, _, same => by
      have lengths := congrArg (fun information => information.2.length) same
      change 0 = (setup.commitRecoverySignals.infoOf who prior).2.length + 1 at lengths
      omega
  | _, _, .extend prior joint legal supported, .start, _, _, same => by
      have lengths := congrArg (fun information => information.2.length) same
      change (setup.commitRecoverySignals.infoOf who prior).2.length + 1 = 0 at lengths
      omega
  | firstAfter, secondAfter, .extend firstPrior firstJoint firstLegal firstSupported,
      .extend secondPrior secondJoint secondLegal secondSupported, firstSurvives, secondSurvives,
      same => by
      have lists := congrArg Prod.snd same
      change (setup.commitRecoverySignals.infoOf who firstPrior).1 ::
          (setup.commitRecoverySignals.infoOf who firstPrior).2 =
        (setup.commitRecoverySignals.infoOf who secondPrior).1 ::
          (setup.commitRecoverySignals.infoOf who secondPrior).2 at lists
      have before : setup.commitRecoverySignals.infoOf who firstPrior =
          setup.commitRecoverySignals.infoOf who secondPrior :=
        Prod.ext (List.cons.inj lists).1 (List.cons.inj lists).2
      have firstBefore : who ∉ (setup.commitRecoveryPublic _).1 := fun excluded =>
        firstSurvives (setup.commitRecovery_step_excluded_subset firstJoint firstLegal
          firstSupported excluded)
      have secondBefore : who ∉ (setup.commitRecoveryPublic _).1 := fun excluded =>
        secondSurvives (setup.commitRecovery_step_excluded_subset secondJoint secondLegal
          secondSupported excluded)
      have earlier := commitRecovery_surviving_ownPlay_eq who firstPrior secondPrior
        firstBefore secondBefore before
      have oldSignal := congrArg Prod.fst before
      rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at oldSignal
      have newSignal := congrArg Prod.fst same
      rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at newSignal
      have jointEq := setup.commitRecovery_surviving_joint_eq who firstJoint secondJoint
        firstLegal secondLegal firstSupported secondSupported firstSurvives secondSurvives
        (congrArg Prod.fst oldSignal) (congrArg Prod.fst newSignal)
      simp only [InfoSignals.ownPlay_extend]
      rw [before, earlier, jointEq]

/-- On surviving source histories, reconstructing the observed signal
transcript also reconstructs the complete auxiliary information state. -/
theorem commitRecovery_surviving_info_eq (who : Player)
    {first second : setup.commitRecoveryProtocol.State}
    (firstTrace : setup.commitRecoveryProtocol.Trace first)
    (secondTrace : setup.commitRecoveryProtocol.Trace second)
    (firstSurvives : who ∉ (setup.commitRecoveryPublic first).1)
    (secondSurvives : who ∉ (setup.commitRecoveryPublic second).1)
    (same : setup.commitRecoverySignals.infoOf who firstTrace =
      setup.commitRecoverySignals.infoOf who secondTrace) :
    setup.commitRecoveryModel.infoOf who firstTrace =
      setup.commitRecoveryModel.infoOf who secondTrace := by
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who firstTrace =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who secondTrace
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf]
  exact Prod.ext same (setup.commitRecovery_surviving_ownPlay_eq who firstTrace secondTrace
    firstSurvives secondSurvives same)

end Vegas.SourceProgram.Setup
