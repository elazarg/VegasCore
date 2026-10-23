/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitPhaseRecovery

/-! # Commitment recovery leaves unrelated owners' complete action words intact -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- An actual source attempt changes only the histories of block owners. -/
theorem CommitPrefix.Attempt.history_eq_of_not_owner
    {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ} {excluded : Finset Player}
    {finished : Config Player L Δ} {afterExcluded : Finset Player}
    (attempt : block.Attempt entry excluded finished afterExcluded)
    (who : Player) (outside : who ∉ block.owners) : finished.history who = entry.history who := by
  induction attempt with
  | nil => rfl
  | @active Γ Δ O P name owner payload fresh guard rest config excluded finished afterExcluded
      active choice missed missingFailure later ih =>
      have different : who ≠ owner := by
        intro same
        exact outside (by simp only [CommitPrefix.owners, Finset.mem_insert]; exact Or.inl same)
      have outsideRest : who ∉ rest.owners := by
        intro member
        exact outside (Finset.mem_insert_of_mem member)
      rw [ih outsideRest]
      exact Function.update_of_ne different _ _
  | @excluded Γ Δ O P name owner payload fresh guard rest config excluded finished afterExcluded
      inactive later ih =>
      have outsideRest : who ∉ rest.owners := by
        intro member
        exact outside (Finset.mem_insert_of_mem member)
      exact ih outsideRest

/-- Closing an unrelated block preserves the complete own word through clean
settlement, retry, and exhausted automatic reconstruction alike. -/
theorem CommitPrefix.Close.history_eq_of_not_owner
    {block : CommitPrefix Γ O Δ P} {entry : CommitCheckpoint Γ}
    {result : CommitCloseResult Γ Δ} (closed : block.Close entry result)
    (who : Player) (outside : who ∉ block.owners) :
    match result with
    | .retry next => next.config.history who = entry.config.history who
    | .settled final _ => final.history who = entry.config.history who := by
  cases closed with
  | retry attempt _ _ => exact attempt.history_eq_of_not_owner who outside
  | clean attempt _ => exact attempt.history_eq_of_not_owner who outside
  | exhausted attempt _ _ =>
      simpa only [CommitPrefix.automatic_history] using
        attempt.history_eq_of_not_owner who outside

end Vegas.SourceProgram
