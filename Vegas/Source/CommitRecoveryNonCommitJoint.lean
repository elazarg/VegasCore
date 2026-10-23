/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryNonCommitPath

/-! # Original legal noncommitment joints determined by their disclosure bits -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem available_move_eq_of_disclosure :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program) (who : Player)
      (first second : CommitRecoveryMove Player L),
      ProtocolState.atCommit program point = false →
      first ∈ ProtocolView.recoveryAvailable who program (ProtocolState.observe who program point) →
      second ∈ ProtocolView.recoveryAvailable who program
        (ProtocolState.observe who program point) →
      OwnAction.disclosure (some first.action) = OwnAction.disclosure (some second.action) →
      first = second := by
  intro Γ O program
  induction program with
  | ret _ =>
      intro point who first second _notCommit firstAvailable
      cases firstAvailable.1
  | sample name fresh law next ih =>
      intro point who first second notCommit firstAvailable secondAvailable same
      cases point with
      | inl config => cases firstAvailable.1
      | inr point => exact ih point who first second notCommit firstAvailable secondAvailable same
  | commit name owner fresh guard next ih =>
      intro point who first second notCommit firstAvailable secondAvailable same
      cases point with
      | inl config => cases notCommit
      | inr point => exact ih point who first second notCommit firstAvailable secondAvailable same
  | reveal published owner name fresh selected unresolved next ih =>
      intro point who first second notCommit firstAvailable secondAvailable same
      cases point with
      | inl config =>
          change (∃ bit, first.action = .reveal owner name bit) ∧ first.missing = false
            at firstAvailable
          change (∃ bit, second.action = .reveal owner name bit) ∧ second.missing = false
            at secondAvailable
          obtain ⟨⟨firstBit, firstAction⟩, firstMissing⟩ := firstAvailable
          obtain ⟨⟨secondBit, secondAction⟩, secondMissing⟩ := secondAvailable
          have bits : firstBit = secondBit := by
            simpa only [firstAction, secondAction, OwnAction.disclosure] using same
          cases first with
          | mk action missing =>
              cases second with
              | mk otherAction otherMissing =>
                  dsimp only at firstAction secondAction firstMissing secondMissing
                  subst action
                  subst otherAction
                  subst missing
                  subst otherMissing
                  cases bits
                  rfl
      | inr point => exact ih point who first second notCommit firstAvailable secondAvailable same

/-- At the same original noncommitment point, active disclosure bits determine
the complete legal joint, including every inactive NONE and omission marker. -/
theorem noncommit_legal_joint_eq_of_disclosure
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (first second : Player → Option (CommitRecoveryMove Player L))
    (notCommit : ProtocolState.atCommit program point = false)
    (firstLegal : GameTheory.Protocol.IsLegalJoint
      (CommitRecoveryState.atPoint point excluded 0).Active
      (CommitRecoveryState.atPoint point excluded 0).available first)
    (secondLegal : GameTheory.Protocol.IsLegalJoint
      (CommitRecoveryState.atPoint point excluded 0).Active
      (CommitRecoveryState.atPoint point excluded 0).available second)
    (same : ∀ who, ProtocolState.actor program point = some who → who ∉ excluded →
      OwnAction.disclosure ((first who).map (·.action)) =
        OwnAction.disclosure ((second who).map (·.action))) : first = second := by
  funext who
  have firstOffered := firstLegal who
  have secondOffered := secondLegal who
  cases firstCell : first who with
  | none =>
      rw [firstCell] at firstOffered
      cases secondCell : second who with
      | none => rfl
      | some secondMove =>
          rw [secondCell] at secondOffered
          exact (firstOffered secondOffered.1).elim
  | some firstMove =>
      rw [firstCell] at firstOffered
      cases secondCell : second who with
      | none =>
          rw [secondCell] at secondOffered
          exact (secondOffered firstOffered.1).elim
      | some secondMove =>
          rw [secondCell] at secondOffered
          have disclosed := same who firstOffered.1.1 firstOffered.1.2
          rw [firstCell, secondCell] at disclosed
          exact congrArg some (available_move_eq_of_disclosure program point who
            firstMove secondMove notCommit firstOffered.2 secondOffered.2 disclosed)

end Vegas.SourceProgram.ProtocolState
