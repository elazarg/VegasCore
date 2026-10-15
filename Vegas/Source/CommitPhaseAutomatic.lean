/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPhaseRecovery

/-! # Excluded commitment phases have their exact automatic source result -/

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
  {entry : Config Player L Γ} {finished : Config Player L Δ} {excluded after : Finset Player}

/-- No active action can occur in an attempt whose entire owner roster is
already excluded. Its environment, guard registry and history are automatic. -/
theorem Attempt.eq_automatic_of_owners
    (attempt : block.Attempt entry excluded finished after) (all : block.owners ⊆ excluded) :
    finished = block.automatic entry ∧ after = excluded := by
  induction attempt with
  | nil => exact ⟨rfl, rfl⟩
  | @active Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      active choice missed missingFailure later ih =>
      exact (active (all (Finset.mem_insert_self _ _))).elim
  | @excluded Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      inactive later ih =>
      exact ih (fun who member => all (Finset.mem_insert_of_mem member))

end Vegas.SourceProgram.CommitPrefix
