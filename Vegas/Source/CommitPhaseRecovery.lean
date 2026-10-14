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

theorem exists_result {finished : Config Player L Δ} {excluded : Finset Player}
    (attempt : block.Attempt entry.config entry.excluded finished excluded) :
    ∃ result, Close block entry result := by
  by_cases empty : attempt.failedOwners = ∅
  · exact ⟨_, .clean attempt empty⟩
  · have failed : attempt.failedOwners.Nonempty := Finset.nonempty_iff_ne_empty.mpr empty
    by_cases survives : (block.owners \ excluded).Nonempty
    · exact ⟨_, .retry attempt failed survives⟩
    · refine ⟨_, .exhausted attempt failed ?_⟩
      intro who member
      by_contra outside
      exact survives ⟨who, Finset.mem_sdiff.mpr ⟨member, outside⟩⟩

theorem excluded_subset (closed : Close block entry result) :
    entry.excluded ⊆ result.excluded := by
  cases closed with
  | retry attempt _ _ => exact attempt.excluded_subset
  | clean attempt _ => exact attempt.excluded_subset
  | exhausted attempt _ _ => exact attempt.excluded_subset

/-- A retry restores the entire semantic checkpoint, with full attempted recall. -/
theorem retry_checkpoint {next : CommitCheckpoint Γ}
    (closed : Close block entry (.retry next)) :
    ∃ (finished : Config Player L Δ) (excluded : Finset Player),
      Nonempty (block.Attempt entry.config entry.excluded finished excluded) ∧
      next.config.state = entry.config.state ∧
      next.config.registry = entry.config.registry ∧
      @next.config.revelations = @entry.config.revelations ∧
      next.config.history = finished.history ∧ next.excluded = excluded ∧
      next.attempt = entry.attempt + 1 ∧
      ∀ who, (entry.config.history who).IsPrefix (next.config.history who) := by
  cases closed with
  | retry attempt _ _ =>
      exact ⟨_, _, ⟨attempt⟩, rfl, rfl, rfl, rfl, rfl, rfl, attempt.history_prefix⟩

private theorem excluded_ssubset {finished : Config Player L Δ} {excluded : Finset Player}
    (attempt : block.Attempt entry.config entry.excluded finished excluded)
    (failed : attempt.failedOwners.Nonempty) : entry.excluded ⊂ excluded := by
  refine ⟨attempt.excluded_subset, ?_⟩
  intro reverse
  obtain ⟨who, member⟩ := failed
  have fresh : who ∉ entry.excluded := Finset.disjoint_left.mp attempt.failed_disjoint member
  apply fresh
  apply reverse
  rw [attempt.excluded_eq]
  exact Finset.mem_union_right _ member

/-- The permanent excluded set supplies a potential for counting actual resets. -/
theorem card_potential (closed : Close block entry result) :
    entry.excluded.card + result.resets ≤ result.excluded.card := by
  cases closed with
  | retry attempt failed _ =>
      exact Finset.card_lt_card (excluded_ssubset attempt failed)
  | clean attempt _ =>
      exact Finset.card_le_card attempt.excluded_subset
  | exhausted attempt _ _ =>
      exact Finset.card_le_card attempt.excluded_subset

/-- A phase with at most one owner has no surviving co-phase binding to void. -/
theorem not_retry_of_single_owner (single : block.owners.card ≤ 1)
    {next : CommitCheckpoint Γ} (closed : Close block entry (.retry next)) : False := by
  cases closed with
  | @retry finished excluded attempt failed survives =>
      obtain ⟨who, failedMember⟩ := failed
      obtain ⟨other, survivor⟩ := survives
      have same := Finset.card_le_one.mp single who (attempt.failed_subset_owners failedMember)
        other (Finset.mem_sdiff.mp survivor).1
      have recorded : who ∈ excluded := by
        rw [attempt.excluded_eq]
        exact Finset.mem_union_right _ failedMember
      exact (Finset.mem_sdiff.mp survivor).2 (same ▸ recorded)

/-- In particular, a singleton commit phase never resets. -/
theorem not_retry_of_singleton (single : block.length ≤ 1)
    {next : CommitCheckpoint Γ} (closed : Close block entry (.retry next)) : False :=
  not_retry_of_single_owner (block.owners_card_le_length.trans single) closed

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

namespace CommitCloseChain

variable {first last : Finset Player} {count : Nat}

theorem card_bound (chain : CommitCloseChain (L := L) first last count) :
    first.card + count ≤ last.card := by
  induction chain with
  | nil => omega
  | close closed later ih =>
      have step := closed.card_potential
      omega

theorem reset_bound [Fintype Player] (chain : CommitCloseChain (L := L) first last count) :
    count ≤ Fintype.card Player := by
  have potential := chain.card_bound
  have bounded := Finset.card_le_univ last
  omega

end CommitCloseChain
end Vegas.SourceProgram
