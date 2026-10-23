/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPhase

/-! # Closing and retrying source commitment phases

A failed active binding restarts the phase only if an owner survives. Semantic
rollback restores the entry checkpoint; private histories keep every voided
choice. Every retry permanently excludes a new owner, bounding all retries.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Permanent exclusion and fresh-attempt identity accompany a semantic checkpoint. -/
structure CommitCheckpoint (Γ : SourceCtx Player L) where
  config : Config Player L Γ
  excluded : Finset Player
  attempt : Nat

namespace CommitCheckpoint

variable {Γ Δ : SourceCtx Player L}

/-- Restore all semantic fields but retain the complete attempted private histories. -/
def retry (entry : CommitCheckpoint Γ) (finished : Config Player L Δ)
    (excluded : Finset Player) : CommitCheckpoint Γ :=
  ⟨{ entry.config with history := finished.history }, excluded, entry.attempt + 1⟩

end CommitCheckpoint

inductive CommitCloseResult (Γ Δ : SourceCtx Player L) where
  | retry (checkpoint : CommitCheckpoint Γ)
  | settled (config : Config Player L Δ) (excluded : Finset Player)

namespace CommitCloseResult

variable {Γ Δ : SourceCtx Player L}

def excluded : CommitCloseResult Γ Δ → Finset Player
  | .retry checkpoint => checkpoint.excluded
  | .settled _ excluded => excluded

def resets : CommitCloseResult Γ Δ → Nat
  | .retry _ => 1
  | .settled _ _ => 0

end CommitCloseResult

namespace CommitPrefix

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Closing uses failures of active bindings only. If no owner survives, the
phase is rebuilt automatically from its entry checkpoint and is not retried. -/
inductive Close (block : CommitPrefix Γ O Δ P) (entry : CommitCheckpoint Γ) :
    CommitCloseResult Γ Δ → Prop where
  | retry {finished : Config Player L Δ} {excluded : Finset Player}
      (attempt : block.Attempt entry.config entry.excluded finished excluded)
      (failed : attempt.failedOwners.Nonempty) (survives : (block.owners \ excluded).Nonempty) :
      Close block entry (.retry (entry.retry finished excluded))
  | clean {finished : Config Player L Δ} {excluded : Finset Player}
      (attempt : block.Attempt entry.config entry.excluded finished excluded)
      (noFailure : attempt.failedOwners = ∅) :
      Close block entry (.settled finished excluded)
  | exhausted {finished : Config Player L Δ} {excluded : Finset Player}
      (attempt : block.Attempt entry.config entry.excluded finished excluded)
      (failed : attempt.failedOwners.Nonempty) (noSurvivor : block.owners ⊆ excluded) :
      Close block entry (.settled
        (block.automatic { entry.config with history := finished.history }) excluded)

namespace Close

variable {block : CommitPrefix Γ O Δ P} {entry : CommitCheckpoint Γ}
  {result : CommitCloseResult Γ Δ}

theorem excluded_subset (closed : Close block entry result) :
    entry.excluded ⊆ result.excluded := by
  cases closed with
  | retry attempt _ _ => exact attempt.excluded_subset
  | clean attempt _ => exact attempt.excluded_subset
  | exhausted attempt _ _ => exact attempt.excluded_subset

end Close
end CommitPrefix

/-- A sequence of actual closes, sharing their permanent exclusion state.
Context changes between phases do not affect the exclusion potential. -/
inductive CommitCloseChain : Finset Player → Finset Player → Nat → Prop where
  | nil (excluded : Finset Player) : CommitCloseChain excluded excluded 0
  | close {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      {block : CommitPrefix Γ O Δ P} {entry : CommitCheckpoint Γ}
      {result : CommitCloseResult Γ Δ} {last : Finset Player} {count : Nat}
      (closed : block.Close entry result)
      (later : CommitCloseChain result.excluded last count) :
      CommitCloseChain entry.excluded last (result.resets + count)
end Vegas.SourceProgram
