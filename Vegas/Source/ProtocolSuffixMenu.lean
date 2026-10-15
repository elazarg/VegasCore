/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolSuffix

/-! # Intended action menus along genuine source suffixes -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolSuffix

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
  {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
  {lift : ProtocolState program → ProtocolState whole}

/-- The same original source action is offered at a suffix point and its whole
program embedding. Earlier instructions introduce no new current choice. -/
theorem intendedAvailable (origin : ProtocolSuffix whole program lift) (who : Player) :
    ∀ point, ProtocolView.intendedAvailable who whole (ProtocolState.observe who whole
        (lift point)) =
      ProtocolView.intendedAvailable who program (ProtocolState.observe who program point) := by
  induction origin with
  | initial => intro point; rfl
  | sampleTail fresh law next _origin ih => intro point; exact ih (.inr point)
  | commitTail fresh guard next _origin ih => intro point; exact ih (.inr point)
  | revealTail fresh selected unresolved next _origin ih =>
      intro point
      exact ih (.inr point)

end Vegas.SourceProgram.ProtocolSuffix
