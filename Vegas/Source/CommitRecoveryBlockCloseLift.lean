/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockClose
import Vegas.Source.CommitRecoveryBlockLift

/-! # Typed commitment closures lift to legal whole-source recovery paths -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A real typed attempt with a fresh miss and a surviving block owner closes
to the exact restored whole source point, retaining the completed own words. -/
theorem Attempt.close_retry_lift
    {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ} {excluded : Finset Player}
    {finished : Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after)
    (suffix : SourceProgram Player L Δ P) (boundary : IsCommitBoundary suffix)
    (positive : 0 < block.length) (generation : Nat)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState whole)
    (ranks : ∀ point, ProtocolState.remaining whole (lift point) =
      ProtocolState.remaining (block.prepend suffix) point)
    (commits : ∀ point, ProtocolState.atCommit whole (lift point) =
      ProtocolState.atCommit (block.prepend suffix) point)
    (owners : ∀ point, ProtocolState.commitOwners whole (lift point) =
      ProtocolState.commitOwners (block.prepend suffix) point)
    (endpoints : ∀ point, ProtocolState.commitEnd whole (lift point) =
      ProtocolState.commitEnd (block.prepend suffix) point)
    (histories : ∀ point, ProtocolState.history whole (lift point) =
      ProtocolState.history (block.prepend suffix) point)
    (memories : ∀ point past, lift (ProtocolState.withHistory (block.prepend suffix) point past) =
      ProtocolState.withHistory whole (lift point) past)
    (failed : attempt.failedOwners.Nonempty) (survives : (block.owners \ after).Nonempty) :
    ((CommitRecoveryState.atPoint
        (lift (ProtocolState.entry (block.prepend suffix) entry)) excluded generation).install
      (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), after)
      (fun _ member => attempt.excluded_subset member)).close =
      CommitRecoveryState.atPoint
        (lift (ProtocolState.entry (block.prepend suffix)
          { entry with history := finished.history })) after (generation + 1) := by
  classical
  have committing : ProtocolState.atCommit (block.prepend suffix)
      (ProtocolState.entry (block.prepend suffix) entry) = true := by
    cases block with
    | nil => cases positive
    | commit => rfl
  have endpoint := block.commitEnd_entry_prepend suffix boundary entry
  simp only [CommitRecoveryState.close, CommitRecoveryState.Finished,
    CommitRecoveryState.NewFailure, CommitRecoveryState.Survives,
    CommitRecoveryState.retry, CommitRecoveryState.restored,
    CommitRecoveryState.install, CommitRecoveryState.atPoint,
    commits, committing, ranks, liftPoint_remaining, ProtocolState.remaining_entry,
    endpoints, endpoint, and_self, attempt.newly_excluded, failed, owners,
    block.commitOwners_entry_prepend suffix boundary entry, survives, ↓reduceIte,
    ← memories, histories, liftPoint_history, ProtocolState.history_entry,
    ProtocolState.withHistory_entry]

/-- Compiler-derived residual control lifts every typed clean, retry or exhausted
closure to the exact settled point of the actual whole-source recovery protocol. -/
theorem Close.reaches_lift
    {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (initial : Config Player L wholeΓ)
    {block : CommitPrefix Γ O Δ P} {entry : CommitCheckpoint Γ}
    {result : CommitCloseResult Γ Δ} (closed : block.Close entry result)
    (suffix : SourceProgram Player L Δ P) (boundary : IsCommitBoundary suffix)
    (positive : 0 < block.length)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState whole)
    (ranks : ∀ point, ProtocolState.remaining whole (lift point) =
      ProtocolState.remaining (block.prepend suffix) point)
    (actors : ∀ point, ProtocolState.actor whole (lift point) =
      ProtocolState.actor (block.prepend suffix) point)
    (menus : ∀ point who, ProtocolView.recoveryAvailable who whole
      (ProtocolState.observe who whole (lift point)) =
      ProtocolView.recoveryAvailable who (block.prepend suffix)
        (ProtocolState.observe who (block.prepend suffix) point))
    (steps : ∀ point excluded joint, ProtocolState.recoveryStep whole (lift point)
      excluded joint =
        (ProtocolState.recoveryStep (block.prepend suffix) point excluded joint).map
          (fun next => (lift next.1, next.2)))
    (commits : ∀ point, ProtocolState.atCommit whole (lift point) =
      ProtocolState.atCommit (block.prepend suffix) point)
    (owners : ∀ point, ProtocolState.commitOwners whole (lift point) =
      ProtocolState.commitOwners (block.prepend suffix) point)
    (endpoints : ∀ point, ProtocolState.commitEnd whole (lift point) =
      ProtocolState.commitEnd (block.prepend suffix) point)
    (automatic : ∀ point, lift (ProtocolState.automaticCommitBlock (block.prepend suffix) point) =
      ProtocolState.automaticCommitBlock whole (lift point))
    (histories : ∀ point, ProtocolState.history whole (lift point) =
      ProtocolState.history (block.prepend suffix) point)
    (memories : ∀ point past, lift (ProtocolState.withHistory (block.prepend suffix) point past) =
      ProtocolState.withHistory whole (lift point) past) :
    (commitRecoveryProtocol whole initial).Reaches
      (CommitRecoveryState.atPoint
        (lift (ProtocolState.entry (block.prepend suffix) entry.config))
        entry.excluded entry.attempt)
      (CommitRecoveryState.atPoint
        (lift (result.recoveryState block suffix entry.attempt).point)
        (result.recoveryState block suffix entry.attempt).excluded
        (result.recoveryState block suffix entry.attempt).generation) := by
  classical
  have committing : ProtocolState.atCommit (block.prepend suffix)
      (ProtocolState.entry (block.prepend suffix) entry.config) = true := by
    cases block with
    | nil => cases positive
    | commit => rfl
  have endpoint := block.commitEnd_entry_prepend suffix boundary entry.config
  have path {finished : Config Player L Δ} {after : Finset Player}
      (attempt : block.Attempt entry.config entry.excluded finished after) :=
    attempt.reaches_closed_lift whole initial suffix lift ranks actors menus steps
      (CommitRecoveryState.atPoint
        (lift (ProtocolState.entry (block.prepend suffix) entry.config))
        entry.excluded entry.attempt)
      rfl rfl ((commits _).trans committing) ((endpoints _).trans endpoint).le positive
  cases closed with
  | clean attempt noFailure =>
      have reached := path attempt
      have noNew : ¬ attempt.failedOwners.Nonempty := by rw [noFailure]; simp
      simpa only [CommitRecoveryState.close, CommitRecoveryState.Finished,
        CommitRecoveryState.NewFailure, CommitRecoveryState.install, CommitRecoveryState.atPoint,
        commits, committing, ranks, liftPoint_remaining, ProtocolState.remaining_entry,
        endpoints, endpoint, and_self, attempt.newly_excluded, noNew, ↓reduceIte,
        CommitCloseResult.recoveryState] using reached
  | retry attempt failed survives =>
      have reached := path attempt
      rw [attempt.close_retry_lift whole suffix boundary positive entry.attempt lift ranks
        commits owners endpoints histories memories failed survives] at reached
      simpa only [CommitCloseResult.recoveryState, CommitCheckpoint.retry,
        CommitRecoveryState.atPoint] using reached
  | @exhausted finished after attempt failed noSurvivor =>
      have reached := path attempt
      have noneLeft : ¬ (block.owners \ after).Nonempty := by
        rintro ⟨owner, member⟩
        exact (Finset.mem_sdiff.mp member).2 (noSurvivor (Finset.mem_sdiff.mp member).1)
      simpa only [CommitRecoveryState.close, CommitRecoveryState.Finished,
        CommitRecoveryState.NewFailure, CommitRecoveryState.Survives,
        CommitRecoveryState.exhausted, CommitRecoveryState.restored,
        CommitRecoveryState.install, CommitRecoveryState.atPoint,
        commits, committing, ranks, liftPoint_remaining, ProtocolState.remaining_entry,
        endpoints, endpoint, and_self, attempt.newly_excluded, failed, owners,
        block.commitOwners_entry_prepend suffix boundary entry.config, noneLeft, ↓reduceIte,
        ← memories, histories, liftPoint_history, ProtocolState.history_entry,
        ProtocolState.withHistory_entry, ← automatic,
        block.automaticCommitBlock_entry_prepend suffix boundary,
        CommitCloseResult.recoveryState] using reached

end Vegas.SourceProgram.CommitPrefix
