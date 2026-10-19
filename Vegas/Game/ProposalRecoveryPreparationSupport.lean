/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryPreparationMenu
import Vegas.Game.ProposalRecoveryPerturbation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Positive source surrogate atoms with no unusable preparation -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Positive omissions still support semantic withholding and actual missing
commitments when the separate unusable-preparation rate is zero. -/
theorem commitRecoveryValueTremble_prepared_support (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) (full : FullSupport values)
    (choice : setup.commitRecoveryModel.Choice who info)
    (prepared : ¬ ProposalRecoveryMove.GeneratedPreparationFailure
      (choice.val.map ProposalRecoveryMove.ordinary)) :
    choice ∈ (setup.commitRecoveryValueTremble who info omission omissionPositive.le
      omissionSmall.le 0 le_rfl zero_le_one values).support := by
  have legal := choice.property
  change setup.commitRecoveryMenu who info choice.val at legal
  cases selected : (choice.val : Option (CommitRecoveryMove Player L)) with
  | none =>
      rw [selected] at legal
      have equal : setup.commitRecoveryFailureChoice who info true = choice := by
        apply Subtype.ext
        rw [selected]
        have otherLegal := (setup.commitRecoveryFailureChoice who info true).property
        cases chosen : (setup.commitRecoveryFailureChoice who info true).val with
        | none => rfl
        | some move =>
            change setup.commitRecoveryMenu who info _ at otherLegal
            rw [chosen] at otherLegal
            exact (legal otherLegal.1).elim
      rw [commitRecoveryValueTremble, ← equal]
      exact mem_support_mix_left _ _ _ omissionPositive
        ((PMF.mem_support_pure_iff _ _).mpr rfl)
  | some move =>
      rw [selected] at legal
      have supported := setup.commitRecoveryValueTremble_fullSupport who info omission
        omissionPositive omissionSmall (1 / 2) (by norm_num) (by norm_num) values full choice
      cases committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program)
      · simpa only [commitRecoveryValueTremble, committing, Bool.false_eq_true, ↓reduceIte]
          using supported
      · simp only [commitRecoveryValueTremble, committing, ↓reduceIte] at supported ⊢
        rw [mix_zero]
        rcases support_mix_subset _ _ _ _ _ supported with omitted | ordinary
        · exact mem_support_mix_left _ _ _ omissionPositive omitted
        · rcases support_mix_subset _ _ _ _ _ ordinary with bad | ordinary
          · have equal : choice = setup.commitRecoveryFailureChoice who info false :=
              (PMF.mem_support_pure_iff _ _).mp bad
            have chosen : (setup.commitRecoveryFailureChoice who info false).val = some move := by
              rw [← equal]
              exact selected
            have properties := setup.commitRecoveryFailureChoice_spec who info false move chosen
            have missing : move.missing = false := by
              simpa only [Bool.and_false] using properties.2
            have generated : ProposalRecoveryMove.GeneratedPreparationFailure
                (choice.val.map ProposalRecoveryMove.ordinary) := by
              rw [selected]
              cases current : info.1.1.1 with
              | none =>
                  have impossible : False := by
                    simpa only [current, Option.elim_none] using legal.2
                  exact impossible.elim
              | some view =>
                  exact ProtocolView.generatedPreparationFailure_of_binding_failure who
                    setup.program view move
                    (by simpa only [current, Option.elim_some] using legal.2)
                    (by simpa only [current, Option.elim_some] using committing)
                    missing properties.1
            exact (prepared generated).elim
          · exact mem_support_mix_right _ _ _ omissionSmall ordinary

end Vegas.SourceProgram.Setup
