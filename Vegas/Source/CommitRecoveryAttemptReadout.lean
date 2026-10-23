/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryClear
import Vegas.Source.ProtocolSuffix

/-! # Original attempt success is an erased boundary readout

The readout checks typed binding values rather than guard predictions. A
failed attempt has changed exclusions even after restoring its saved cells.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Config

/-- Every binding of the selected owner holds a typed value; guards are not
tested. Accepted failed bindings violate this observable property. -/
def BindingsHoldValues {Γ : SourceCtx Player L} (who : Player) (config : Config Player L Γ) :
    Prop :=
  ∀ {name : VarId} {payload : L.Ty} (cell : HasVar Γ name (.commitment who payload)),
    ∃ value, config.state.get cell = .success value

end Config

variable [IExpr.ResultTypes L]

namespace ProtocolState

/-- Read successful own bindings at the actual current typed source cursor. -/
def BindingsHoldValues (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _, config => Config.BindingsHoldValues who config
  | _, _, .sample _ _ _ next, point =>
      point.elim (Config.BindingsHoldValues who) (BindingsHoldValues who next)
  | _, _, .commit _ _ _ _ next, point =>
      point.elim (Config.BindingsHoldValues who) (BindingsHoldValues who next)
  | _, _, .reveal _ _ _ _ _ _ next, point =>
      point.elim (Config.BindingsHoldValues who) (BindingsHoldValues who next)

theorem bindingsHoldValues_entry {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    BindingsHoldValues who program (entry program config) ↔ config.BindingsHoldValues who := by
  cases program <;> rfl

theorem bindingsHoldValues_withHistory (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    BindingsHoldValues who program (withHistory program point past) ↔
      BindingsHoldValues who program point
  | _, _, .ret _, _, _ => Iff.rfl
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact bindingsHoldValues_withHistory who next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact bindingsHoldValues_withHistory who next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact bindingsHoldValues_withHistory who next point past

end ProtocolState

namespace ProtocolSuffix

theorem bindingsHoldValues_lift {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) : ∀ point,
    ProtocolState.BindingsHoldValues who whole (lift point) ↔
      ProtocolState.BindingsHoldValues who program point := by
  induction origin with
  | initial => intro point; rfl
  | sampleTail _ _ _ _ ih => exact fun point => ih (.inr point)
  | commitTail _ _ _ _ ih => exact fun point => ih (.inr point)
  | revealTail _ _ _ _ _ ih => exact fun point => ih (.inr point)

end ProtocolSuffix

namespace CommitPrefix

theorem bindingsHoldValues_liftPoint {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P) (who : Player)
    (point : ProtocolState suffix) :
    ProtocolState.BindingsHoldValues who (block.prepend suffix) (block.liftPoint suffix point) ↔
      ProtocolState.BindingsHoldValues who suffix point := by
  induction block with
  | nil => rfl
  | commit _ _ _ _ _ ih => exact ih suffix point

end CommitPrefix

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

/-- Relative to the ORIGINAL entry exclusions, closing changes no success
readout. Retry and exhaustion fail its exclusion test before restored cells
can be mistaken for successful old bindings. -/
theorem close_success_readout (state : CommitRecoveryState program) (who : Player) :
    (state.close.excluded = state.entryExcluded ∧
      ProtocolState.BindingsHoldValues who program state.close.point) ↔
    (state.excluded = state.entryExcluded ∧
      ProtocolState.BindingsHoldValues who program state.point) := by
  rw [close_excluded]
  by_cases same : state.excluded = state.entryExcluded
  · have clear : ¬ state.NewFailure := by simp only [NewFailure, same, Finset.sdiff_self,
      Finset.not_nonempty_empty, not_false_eq_true]
    rw [state.close_point_of_no_new_failure clear]
  · simp only [same, false_and]

end CommitRecoveryState
end Vegas.SourceProgram
