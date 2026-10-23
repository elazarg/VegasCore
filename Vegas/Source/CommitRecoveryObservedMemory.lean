/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasedStep
import Vegas.Source.ProtocolSuffix

/-! # Typed current observations with independent remembered-word projection -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}


/-- Select the remembered-word part of an existing typed decision view.
Both choices keep every current typed cell. -/
def DecisionView.historyProjection {who : Player} {Γ : SourceCtx Player L}
    (remember : Bool) (view : DecisionView (L := L) who Γ) : DecisionView who Γ :=
  if remember then view else (view.1, [])

/-- The semantic projection removes only the current remembered word; it
preserves the actual source cursor and the entire live typed observation. -/
def ProtocolView.historyProjection (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (remember : Bool) (view : ProtocolView who program) : ProtocolView who program :=
  if remember then view else eraseHistory who program view

/-- Actual suffix lifts commute with replacing remembered words. -/
theorem ProtocolSuffix.withHistory_lift
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    ∀ point past, lift (ProtocolState.withHistory program point past) =
      ProtocolState.withHistory whole (lift point) past := by
  induction origin with
  | initial => intro point past; rfl
  | sampleTail fresh law next previous ih => exact fun point past => ih (.inr point) past
  | commitTail fresh guard next previous ih => exact fun point past => ih (.inr point) past
  | revealTail fresh selected unresolved next previous ih =>
      exact fun point past => ih (.inr point) past

/-- The actual information retained when comparing source instruction chunks. -/
inductive SourceViewProjection where
  | memory (remember : Bool)
  | publicOnly

/-- Project a genuine typed view without changing its cursor. Public projection
is used only for older chunks whose private declarations have been voided. -/
def SourceViewProjection.apply (projection : SourceViewProjection) (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (view : ProtocolView who program) : ProtocolView who program :=
  match projection with
  | .memory remember => ProtocolView.historyProjection who program remember view
  | .publicOnly => ProtocolView.publicOnly who program view

end Vegas.SourceProgram
