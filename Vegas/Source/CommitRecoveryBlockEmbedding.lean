/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryProtocol

/-! # Source points after a typed commitment prefix -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Place a suffix point after every commitment in the typed prefix. -/
def liftPoint : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : CommitPrefix Γ O Δ P) → (suffix : SourceProgram Player L Δ P) →
      ProtocolState suffix → ProtocolState (block.prepend suffix)
  | _, _, _, _, .nil, _, point => point
  | _, _, _, _, .commit _ _ _ _ rest, suffix, point => Sum.inr (rest.liftPoint suffix point)

theorem instructionCount_prepend {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P) :
    instructionCount (block.prepend suffix) = block.length + instructionCount suffix := by
  induction block with
  | nil => simp only [prepend, length, Nat.zero_add]
  | commit _ _ _ _ _ ih =>
      simp only [prepend, instructionCount, ih, length]
      omega

theorem liftPoint_remaining {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (point : ProtocolState suffix) :
    ProtocolState.remaining (block.prepend suffix) (block.liftPoint suffix point) =
      ProtocolState.remaining suffix point := by
  induction block with
  | nil => rfl
  | commit _ _ _ _ _ ih => exact ih suffix point

theorem liftPoint_history {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (point : ProtocolState suffix) :
    ProtocolState.history (block.prepend suffix) (block.liftPoint suffix point) =
      ProtocolState.history suffix point := by
  induction block with
  | nil => rfl
  | commit _ _ _ _ _ ih => exact ih suffix point

theorem commitEnd_entry_prepend {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (boundary : IsCommitBoundary suffix) (config : Config Player L Γ) :
    ProtocolState.commitEnd (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) config) = instructionCount suffix := by
  rw [ProtocolState.commitEnd_entry]
  have endpoint : instructionCount (commitPhase (block.prepend suffix)).suffix =
      instructionCount suffix := by
    induction block with
    | nil => cases suffix <;> trivial
    | commit _ _ _ _ _ ih => exact ih suffix boundary (automaticCommit _ _ _ config)
  exact endpoint

theorem automaticCommitBlock_entry_prepend {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (boundary : IsCommitBoundary suffix) (config : Config Player L Γ) :
    ProtocolState.automaticCommitBlock (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) config) =
      block.liftPoint suffix (ProtocolState.entry suffix (block.automatic config)) := by
  induction block with
  | nil => cases suffix <;> trivial
  | commit _ _ _ _ _ ih => exact congrArg Sum.inr (ih suffix boundary _)

theorem commitOwners_entry_prepend {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (boundary : IsCommitBoundary suffix) (config : Config Player L Γ) :
    ProtocolState.commitOwners (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) config) = block.owners := by
  have owners : (commitPhase (block.prepend suffix)).block.owners = block.owners := by
    induction block with
    | nil => cases suffix <;> trivial
    | commit _ _ _ _ _ ih =>
        simp only [prepend, commitPhase, CommitPrefix.owners]
        exact congrArg (insert _) (ih suffix boundary (automaticCommit _ _ _ config))
  cases block with
  | nil => cases suffix <;> trivial
  | commit => exact owners

end Vegas.SourceProgram.CommitPrefix
