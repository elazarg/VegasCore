/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.CommitPrefixCompletion
import Vegas.Source.IntendedCommitPredecessor
import Vegas.Source.CommitBlockInformation

/-! # Intended completion of hidden foreign commitment cells -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Own admissibility at the end of a filled typed prefix reflects to its entry,
regardless of the failed hidden foreign values used in that reference fill. -/
theorem fillCommitPrefix_intendedFor_entry {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (store : Store (graphLayout whole))
    (entry : SourceProgram.Config Player L Γ) (who : Player)
    (after : (fillCommitPrefix whole block suffix embedding store entry).IntendedFor who P) :
    entry.IntendedFor who O := by
  induction block with
  | nil => exact after
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      have head := ih suffix _ _ after
      exact SourceProgram.Config.IntendedFor.commit_before fresh guard entry _ head

end Vegas
