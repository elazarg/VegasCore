/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryAttemptSuccess
import Vegas.Source.ProtocolSuffix

/-! # Standing accepted failures in an original commitment attempt

A failed own raw result creates a concrete unresolved failed cell. Without
an omission reset, the completed attempt checkpoints that debt permanently.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace CommitPrefix.Attempt

/-- A failed raw action in the actual typed attempt leaves an unresolved
failed binding at its completed pre-restore configuration. -/
theorem failedBinding_of_failed_joint
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after)
    (who : Player) (unique : (Γ.map Prod.fst).Nodup)
    (joint : Player → Option (CommitRecoveryMove Player L)) (member : joint ∈ attempt.joints)
    (move : CommitRecoveryMove Player L) (selected : joint who = some move)
    (failed : move.action.IsFailure) : finished.FailedBinding who P := by
  induction attempt with
  | nil => simp only [joints, List.not_mem_nil] at member
  | @active Γ Δ O P name owner payload fresh guard rest config excluded finished after
      active choice missed missingFailure later ih =>
      rcases List.mem_cons.mp member with rfl | kept
      · by_cases same : who = owner
        · subst who
          simp only [↓reduceIte, Option.some.injEq] at selected
          subst move
          cases choice with
          | success value => cases failed
          | failure =>
              exact later.preserves_failedBinding owner
                (Config.failedBinding_commit config unique fresh guard O)
        · simp only [same, ↓reduceIte] at selected
          cases selected
      · exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) kept
  | @excluded Γ Δ O P name owner payload fresh guard rest config excluded finished after
      inactive later ih =>
      rcases List.mem_cons.mp member with rfl | kept
      · cases selected
      · exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) kept

end CommitPrefix.Attempt

variable [IExpr.ResultTypes L]

namespace CommitPrefix

/-- Embedding the completed suffix after the commitment constructors retains
its actual unresolved failed cell. -/
theorem failedBinding_liftPoint
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (who : Player) (point : ProtocolState suffix)
    (failed : ProtocolState.FailedBinding who suffix point) :
    ProtocolState.FailedBinding who (block.prepend suffix) (block.liftPoint suffix point) := by
  induction block with
  | nil => exact failed
  | commit name owner fresh guard rest ih => exact ih suffix point failed

end CommitPrefix

namespace ProtocolSuffix

/-- A genuine original suffix lifts unresolved failed bindings to the whole
program, including after earlier reveal constructors. -/
theorem failedBinding_lift
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) (point : ProtocolState program)
    (failed : ProtocolState.FailedBinding who program point) :
    ProtocolState.FailedBinding who whole (lift point) := by
  induction origin with
  | initial => exact failed
  | sampleTail fresh law next previous ih => exact ih (.inr point) failed
  | commitTail fresh guard next previous ih => exact ih (.inr point) failed
  | revealTail fresh selected unresolved next previous ih => exact ih (.inr point) (Or.inr failed)

end ProtocolSuffix

namespace CommitRecoveryState

/-- A real clean close checkpoints newly created live debt; it does not
require that debt to have existed in the saved state before the attempt. -/
theorem close_checkpointed_owesFailure
    {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
    (state : CommitRecoveryState program) (who : Player) (finished : state.Finished)
    (clean : ¬ state.NewFailure) (owed : ProtocolState.OwesFailure who program state.point) :
    ProtocolState.OwesFailure who program state.close.saved ∧
      ProtocolState.OwesFailure who program state.close.point := by
  simpa only [close, finished, clean, ↓reduceIte, atPoint] using And.intro owed owed

end CommitRecoveryState
end Vegas.SourceProgram
