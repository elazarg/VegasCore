/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryChoiceFloor
import Vegas.Game.CommitRecoveryClearDecoder

/-! # A positive omission floor at genuine clear binding decisions -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- An active source binding admits an actual omission, separately from an
accepted unusable binding. Its atom is bounded by the genuine-site floor. -/
theorem commitRecovery_missing_floor (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (floor : ℝ)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ (assessment.strategy who site.1 choice).toReal)
    (who : Player) (view : SourceProgram.ProtocolView who setup.program)
    (actor : ProtocolView.actor who setup.program view = some who)
    (binding : ProtocolView.atCommit who setup.program view = true)
    (played : setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryClearInformation wellFormed who (some view))) :
    floor ≤ (((assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who (some view))).map
        (fun choice => CommitRecoveryMove.missed choice.1)) true).toReal := by
  classical
  obtain ⟨offered, legal, failed⟩ := ProtocolView.exists_failure_menu who setup.program
    (CommitmentInterface.forfeiture setup.program) (fun _ => rfl) view
  cases offered with
  | none => exact False.elim (legal actor)
  | some action =>
    let information := setup.commitRecoveryClearInformation wellFormed who (some view)
    have current := setup.commitRecoveryClearInformation_current wellFormed who (some view)
    have excluded := setup.commitRecoveryClearInformation_excluded wellFormed who (some view)
    let choice : setup.commitRecoveryModel.Choice who information :=
      ⟨some ⟨action, true⟩, by
        change setup.commitRecoveryMenu who information (some ⟨action, true⟩)
        change setup.commitRecoveryActive who information.1.1 ∧
          information.1.1.1.elim False (fun observed =>
            (⟨action, true⟩ : CommitRecoveryMove Player L) ∈
              ProtocolView.recoveryAvailable who setup.program observed)
        constructor
        · unfold commitRecoveryActive
          dsimp only [information]
          rw [current, excluded]
          exact ⟨actor, by simp⟩
        · dsimp only [information]
          rw [current]
          exact ⟨legal.2, by
            simp only [binding, ↓reduceIte]
            exact fun _ => failed action rfl⟩⟩
    apply (floored who ⟨information, played⟩ choice).trans
    apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    rw [PMF.map_apply]
    have term := ENNReal.le_tsum (f := fun other :
      setup.commitRecoveryModel.Choice who information =>
        @ite ENNReal (true = CommitRecoveryMove.missed other.1)
          (Classical.propDecidable _) (assessment.strategy who information other) 0) choice
    simpa only [choice, CommitRecoveryMove.missed, Option.elim_some, ite_true] using term

end Vegas.SourceProgram.Setup
