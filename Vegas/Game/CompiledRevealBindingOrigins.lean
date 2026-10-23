/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceRevealTail
import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Source.CommitRecoveryAttemptReadout
import Vegas.Pending.PhaseStoredCheckpoint

/-! # Original commitment references through compiled disclosure prefixes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Disclosure adds publication cells only. Every remaining commitment keeps
its original context reference, without an intended-play or guard premise. -/
theorem revealTailRefs_commitment_origin :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) {name : VarId} {owner : Player} {payload : L.Ty}
      (selected : HasVar (revealTail count program prefixed).context name
        (.commitment owner payload)),
      ∃ original : HasVar Γ name (.commitment owner payload),
        (revealTailRefs setup count program prefixed refs embedding).get selected =
          refs.get original := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed refs embedding name owner payload selected
      exact ⟨selected, rfl⟩
  | succ count ih =>
      intro Γ names program prefixed refs embedding name who sort selected
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh source unresolved next =>
          obtain ⟨original, equal⟩ := ih next prefixed _
            (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) selected
          cases original with
          | there original => exact ⟨original, equal⟩

/-- A proper saved binding keeps the same typed value at an actual publication
frontier. The reference is the original one retained by the compiler. -/
theorem RecoverySourceCheckpoint.publication_binding_value
    {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) (stored : state.StoredCheckpoint)
    (count : Nat) (prefixed : RevealPrefix checkpoint.residual.tail count)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (selected : HasVar (revealTail count checkpoint.residual.tail prefixed).context name
      (.commitment owner payload))
    (proper : checkpoint.source.BindingsHoldValues owner) :
    ∃ value,
      ((revealTailRefs setup count checkpoint.residual.tail prefixed checkpoint.refs
        checkpoint.embedding).get selected).get? state.current.native.config.store =
          some (.success value) := by
  obtain ⟨original, reference⟩ := revealTailRefs_commitment_origin setup count
    checkpoint.residual.tail prefixed checkpoint.refs checkpoint.embedding selected
  obtain ⟨value, saved⟩ := proper original
  refine ⟨value, ?_⟩
  rw [reference]
  have read := (checkpoint.refs.get original).get?_preserved state.entry.native.config.store
    state.current.native.config.store stored _ (checkpoint.agrees original)
  exact read.trans (congrArg some saved)

end Vegas
