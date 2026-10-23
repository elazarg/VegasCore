/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryExtraChoice
import Vegas.Source.CommitRecoveryContinuingMenu
import Vegas.Game.CommitRecoveryDebtPayoff
import Vegas.Game.CommitRecoveryVoluntaryFailurePayoff
import Vegas.Game.ExclusionMoveExtension
import Vegas.Game.RecoveryCommitPrefixWitness
import Vegas.Game.CommitPrefixReadyRecall
import Vegas.Game.RecoveryBindingPrefix
import GameTheoryExtensions.Analysis.Protocol.SingleMoverReach
import GameTheoryExtensions.Analysis.Protocol.RestrictedComponentCompletion

/-! # Opening-choice factors along genuine source recovery histories -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem nonfailure_noncommit_unique (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program)
      (_notCommit : ProtocolView.atCommit who program view = false)
      (first second : OwnAction Player L),
      first ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program) view →
      second ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program) view →
      ¬ first.IsFailure → ¬ second.IsFailure → first = second
 := by
  intro Γ O program
  induction program with
  | ret payoffs => intro view notCommit first second left; exact left.elim
  | sample name fresh law next ih =>
      intro view notCommit first second left right lf rf
      cases view with
      | inl _ => exact left.elim
      | inr view => exact ih view notCommit first second left right lf rf
  | commit name owner fresh guard next ih =>
      intro view notCommit first second left right lf rf
      cases view with
      | inl _ => cases notCommit
      | inr view => exact ih view notCommit first second left right lf rf
  | reveal published owner name fresh source unresolved next ih =>
      intro view notCommit first second left right lf rf
      cases view with
      | inl _ =>
          obtain ⟨leftFlag, rfl⟩ := left
          obtain ⟨rightFlag, rfl⟩ := right
          have leftTrue : leftFlag = true := by
            cases leftFlag <;> simp_all only [OwnAction.IsFailure, not_true_eq_false]
          have rightTrue : rightFlag = true := by
            cases rightFlag <;> simp_all only [OwnAction.IsFailure, not_true_eq_false]
          rw [leftTrue, rightTrue]
      | inr view => exact ih view notCommit first second left right lf rf

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem continuing_noncommit_unique (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (notCommit : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = false)
    (first second : setup.commitRecoveryModel.Choice who info)
    (left : setup.CommitRecoveryContinues who info first.val)
    (right : setup.CommitRecoveryContinues who info second.val) : first = second := by
  apply Subtype.ext
  have firstLegal := first.property
  have secondLegal := second.property
  cases firstEq : first.val with
  | none =>
      cases secondEq : second.val with
      | none => rfl
      | some second =>
          rw [firstEq] at firstLegal
          change ¬ setup.commitRecoveryActive who info.1.1 at firstLegal
          rw [secondEq] at secondLegal
          change setup.commitRecoveryMenu who info (some second) at secondLegal
          exact (firstLegal secondLegal.1).elim
  | some first =>
      cases secondEq : second.val with
      | none =>
          rw [secondEq] at secondLegal
          rw [firstEq] at firstLegal
          exact (secondLegal firstLegal.1).elim
      | some second =>
          rw [firstEq] at firstLegal
          rw [secondEq] at secondLegal
          have leftFacts := left first firstEq
          have rightFacts := right second secondEq
          have actions : first.action = second.action := by
            cases viewed : info.1.1.1 with
            | none => simpa only [viewed, Option.elim_none] using firstLegal.2
            | some view =>
                apply nonfailure_noncommit_unique who setup.program view
                  (by simpa only [viewed, Option.elim_some] using notCommit)
                  first.action second.action
                · have offered : first ∈ ProtocolView.recoveryAvailable who setup.program
                      view := by simpa only [viewed, Option.elim_some] using firstLegal.2
                  exact offered.1
                · have offered : second ∈ ProtocolView.recoveryAvailable who setup.program
                      view := by simpa only [viewed, Option.elim_some] using secondLegal.2
                  exact offered.1
                · exact leftFacts.2 notCommit
                · exact rightFacts.2 notCommit
          have same : first = second := by
            cases first
            cases second
            simp_all only
          exact congrArg some same

variable [Fintype Player] (wellFormed : setup.WellFormed)
  (reference target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    reference target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

end Setup
end Vegas.SourceProgram
