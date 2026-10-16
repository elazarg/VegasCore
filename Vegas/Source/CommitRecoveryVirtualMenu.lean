/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryVirtualView

/-! # Source menus at deterministic virtual typed views -/

namespace Vegas.SourceProgram.ProtocolView

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Virtual typed views already discard the remembered source action word. -/
theorem eraseHistory_virtualBindings (who : Player) (preserved : Finset VarId) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      eraseHistory who program (virtualBindings who preserved program view) =
        virtualBindings who preserved program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view with
      | inl => rfl
      | inr view => exact congrArg Sum.inr (eraseHistory_virtualBindings who preserved next view)
  | _, _, .commit _ _ _ _ next, view => by
      cases view with
      | inl => rfl
      | inr view => exact congrArg Sum.inr (eraseHistory_virtualBindings who preserved next view)
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view with
      | inl => rfl
      | inr view => exact congrArg Sum.inr (eraseHistory_virtualBindings who preserved next view)

/-- Virtual declarations preserve the source action menu under every admission
interface, since admission depends on the source cursor rather than values. -/
theorem available_virtualBindings (who : Player) (preserved : Finset VarId) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
      (view : ProtocolView who program),
      available who program admission (virtualBindings who preserved program view) =
        available who program admission view
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, admission, view => by
      cases view <;> simp only [virtualBindings, available, Sum.elim_inl, Sum.elim_inr,
        available_virtualBindings who preserved next]
  | _, _, .commit _ _ _ _ next, admission, view => by
      cases view <;> simp only [virtualBindings, available, Sum.elim_inl, Sum.elim_inr,
        available_virtualBindings who preserved next]
  | _, _, .reveal _ _ _ _ _ _ next, admission, view => by
      cases view <;> simp only [virtualBindings, available, Sum.elim_inl, Sum.elim_inr,
        available_virtualBindings who preserved next]

end Vegas.SourceProgram.ProtocolView
