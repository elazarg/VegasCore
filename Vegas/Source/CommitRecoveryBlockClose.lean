/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockPath

/-! # Typed maximal commitment closure is realized by the actual source protocol -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem ProtocolState.withHistory_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (past : History Player L) :
    withHistory program (entry program config) past =
      entry program {config with history := past} := by
  cases program <;> rfl

namespace CommitCloseResult

/-- A typed settled result is at its suffix; a retry returns to its original
source commitment frontier with the newly allocated global generation. -/
def recoveryState {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (generation : Nat) : CommitCloseResult Γ Δ → CommitRecoveryState (block.prepend suffix)
  | .retry checkpoint => CommitRecoveryState.atPoint
      (ProtocolState.entry (block.prepend suffix) checkpoint.config) checkpoint.excluded
        checkpoint.attempt
  | .settled finished excluded => CommitRecoveryState.atPoint
      (block.liftPoint suffix (ProtocolState.entry suffix finished)) excluded generation

end CommitCloseResult

namespace CommitPrefix

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
  {entry : CommitCheckpoint Γ} {result : CommitCloseResult Γ Δ}

/-- Every checked typed clean/retry/exhausted closure is an actual path of
legal instructions in the existing source recovery execution protocol. -/
theorem Close.reaches (closed : block.Close entry result)
    (suffix : SourceProgram Player L Δ P) (boundary : IsCommitBoundary suffix)
    (positive : 0 < block.length) :
    (commitRecoveryProtocol (block.prepend suffix) entry.config).Reaches
      (CommitRecoveryState.atPoint
        (ProtocolState.entry (block.prepend suffix) entry.config) entry.excluded entry.attempt)
      (result.recoveryState block suffix entry.attempt) := by
  classical
  have committing : ProtocolState.atCommit (block.prepend suffix)
      (ProtocolState.entry (block.prepend suffix) entry.config) = true := by
    cases block with
    | nil => cases positive
    | commit => rfl
  have endpoint := block.commitEnd_entry_prepend suffix boundary entry.config
  have path {finished : Config Player L Δ} {after : Finset Player}
      (attempt : block.Attempt entry.config entry.excluded finished after) :=
    attempt.reaches_closed_lift (block.prepend suffix) entry.config suffix id
      (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun point excluded joint => (PMF.map_id _).symm)
      (CommitRecoveryState.atPoint
        (ProtocolState.entry (block.prepend suffix) entry.config) entry.excluded entry.attempt)
      rfl rfl committing endpoint positive
  cases closed with
  | clean attempt noFailure =>
      have reached := path attempt
      have noNew : ¬ (attempt.failedOwners.Nonempty) := by rw [noFailure]; simp
      simpa only [CommitRecoveryState.close, CommitRecoveryState.Finished,
        CommitRecoveryState.NewFailure, CommitRecoveryState.install, CommitRecoveryState.atPoint,
        id_eq, committing, liftPoint_remaining, ProtocolState.remaining_entry, endpoint,
        and_self, attempt.newly_excluded, noNew, ↓reduceIte, CommitCloseResult.recoveryState]
        using reached
  | retry attempt failed survives =>
      have reached := path attempt
      simpa only [CommitRecoveryState.close, CommitRecoveryState.Finished,
        CommitRecoveryState.NewFailure, CommitRecoveryState.Survives,
        CommitRecoveryState.retry, CommitRecoveryState.restored,
        CommitRecoveryState.install, CommitRecoveryState.atPoint,
        id_eq, committing, liftPoint_remaining, ProtocolState.remaining_entry, endpoint,
        and_self, attempt.newly_excluded, failed, block.commitOwners_entry_prepend suffix
          boundary entry.config, survives, ↓reduceIte, liftPoint_history,
        ProtocolState.history_entry, ProtocolState.withHistory_entry,
        CommitCloseResult.recoveryState, CommitCheckpoint.retry] using reached
  | @exhausted finished after attempt failed noSurvivor =>
      have reached := path attempt
      have noneLeft : ¬ (block.owners \ after).Nonempty := by
        rintro ⟨owner, member⟩
        exact (Finset.mem_sdiff.mp member).2 (noSurvivor (Finset.mem_sdiff.mp member).1)
      simpa only [CommitRecoveryState.close, CommitRecoveryState.Finished,
        CommitRecoveryState.NewFailure, CommitRecoveryState.Survives,
        CommitRecoveryState.exhausted, CommitRecoveryState.restored,
        CommitRecoveryState.install, CommitRecoveryState.atPoint,
        id_eq, committing, liftPoint_remaining, ProtocolState.remaining_entry, endpoint,
        and_self, attempt.newly_excluded, failed, block.commitOwners_entry_prepend suffix
          boundary entry.config, noneLeft, ↓reduceIte, liftPoint_history,
        ProtocolState.history_entry, ProtocolState.withHistory_entry,
        block.automaticCommitBlock_entry_prepend suffix boundary,
        CommitCloseResult.recoveryState] using reached

end CommitPrefix
end Vegas.SourceProgram
