/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryProtocol

/-! # Actual legal disclosure actions at noncommitment source instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem ProtocolState.recoveryAvailable_reveal_of_not_commit (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      actor program point = some who → atCommit program point = false →
      ∀ move ∈ ProtocolView.recoveryAvailable who program (observe who program point),
        ∃ name bit, move = (⟨.reveal who name bit, false⟩ : CommitRecoveryMove Player L)
  | _, _, .ret _, _, active, _, _, _ => by cases active
  | _, _, .sample _ _ _ next, point, active, notCommit, move, offered => by
      cases point with
      | inl _ => cases active
      | inr point =>
          exact recoveryAvailable_reveal_of_not_commit who next point active notCommit move offered
  | _, _, .commit _ _ _ _ next, point, active, notCommit, move, offered => by
      cases point with
      | inl _ => cases notCommit
      | inr point =>
          exact recoveryAvailable_reveal_of_not_commit who next point active notCommit move offered
  | _, _, .reveal _ owner name _ _ _ next, point, active, notCommit, move, offered => by
      cases point with
      | inl _ =>
          have same : owner = who := Option.some.inj active
          subst owner
          rcases move with ⟨action, missing⟩
          change (∃ bit, action = .reveal who name bit) ∧ missing = false at offered
          obtain ⟨⟨bit, actionEq⟩, missingEq⟩ := offered
          exact ⟨name, bit, by cases actionEq; cases missingEq; rfl⟩
      | inr point =>
          exact recoveryAvailable_reveal_of_not_commit who next point active notCommit move offered

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem commitRecovery_reveal_joint_of_legal (current : CommitRecoveryState setup.program)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint) (who : Player)
    (active : ProtocolState.actor setup.program current.point = some who)
    (survives : who ∉ current.excluded)
    (notCommit : ProtocolState.atCommit setup.program current.point = false) :
    ∃ name bit, joint who = some (⟨.reveal who name bit, false⟩ : CommitRecoveryMove Player L) := by
  have offered := setup.commitRecoveryProtocol.legalOption_of_legal legal who
  cases selected : joint who with
  | none =>
      have inactive : ¬ setup.commitRecoveryProtocol.active (some current) who := by
        simpa only [selected, LegalOption] using offered
      exact False.elim (inactive ⟨active, survives⟩)
  | some move =>
      rw [selected] at offered
      obtain ⟨name, bit, same⟩ := ProtocolState.recoveryAvailable_reveal_of_not_commit who
        setup.program current.point active notCommit move offered.2
      exact ⟨name, bit, congrArg some same⟩

end Setup
end Vegas.SourceProgram
