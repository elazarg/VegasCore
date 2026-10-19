/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryRevealMenu

/-! # A legal reveal action identifies a noncommitment source cursor -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem ProtocolState.not_atCommit_of_recoveryAvailable_reveal (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (move : CommitRecoveryMove Player L),
      move ∈ ProtocolView.recoveryAvailable who program (observe who program point) →
      (∃ owner name bit, move.action = .reveal owner name bit) →
        atCommit program point = false
  | _, _, .ret _, _, _, offered, _ => by cases offered.1
  | _, _, .sample _ _ _ next, point, move, offered, revealing => by
      cases point with
      | inl _ => rfl
      | inr later =>
          exact not_atCommit_of_recoveryAvailable_reveal who next later move offered revealing
  | _, _, .commit _ _ _ _ next, point, move, offered, revealing => by
      cases point with
      | inl _ =>
          obtain ⟨owner, name, bit, same⟩ := revealing
          obtain ⟨value, _permitted, action⟩ := offered.1
          rw [same] at action
          cases action
      | inr later =>
          exact not_atCommit_of_recoveryAvailable_reveal who next later move offered revealing
  | _, _, .reveal _ _ _ _ _ _ next, point, move, offered, revealing => by
      cases point with
      | inl _ => rfl
      | inr later =>
          exact not_atCommit_of_recoveryAvailable_reveal who next later move offered revealing

end Vegas.SourceProgram
