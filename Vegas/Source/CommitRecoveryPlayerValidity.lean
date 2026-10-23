/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryDebt

/-! # Guard-safe play through actual source recovery

The existing player-specific validity predicate survives arbitrary foreign
actions, automatic foreign slots, and the real checkpoint close.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

theorem commitOwners_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    commitOwners program (entry program config) = (commitPhase program).block.owners := by
  cases program <;> rfl

theorem commitOwners_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    commitOwners program (withHistory program point past) = commitOwners program point
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact commitOwners_withHistory next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact commitOwners_withHistory next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact commitOwners_withHistory next point past

end ProtocolState
end Vegas.SourceProgram
