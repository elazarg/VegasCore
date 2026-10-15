/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitOmissions

/-! # Exclusion readback of decoded source commitment attempts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

/-- The source decoder grows exclusion by precisely the physical missing receipts,
including the harmless repetition of owners excluded at an earlier slot. -/
theorem decodeCommitAttempt_excluded_eq {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) :
    (decodeCommitAttempt whole mode block suffix embedding native entry excluded).2.1 =
      excluded ∪ commitMissingOwners whole mode block suffix embedding native := by
  induction block generalizing excluded with
  | nil => simp only [decodeCommitAttempt, commitMissingOwners, Finset.union_empty]
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      by_cases inactive : owner ∈ excluded
      · dsimp only [decodeCommitAttempt, commitMissingOwners, OutputEmbedding.tail,
          SourceProgram.CommitPrefix.prepend]
        rw [dite_eq_left inactive]
        rw [ih]
        split
        · rw [Finset.union_insert, Finset.insert_eq_of_mem
            (Finset.mem_union_left _ inactive)]
        · rfl
      · dsimp only [decodeCommitAttempt, commitMissingOwners, OutputEmbedding.tail,
          SourceProgram.CommitPrefix.prepend]
        rw [dite_eq_right inactive]
        rw [ih]
        cases accepted : native.accepted (.inr (embedding.event ⟨0, by
          simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩)) with
        | none => simp only [Option.isNone_none, excludeCommit, ↓reduceIte,
            Finset.insert_union, Finset.union_insert]
        | some candidate => simp only [Option.isNone_some, excludeCommit, ↓reduceIte,
            reduceCtorEq]

end Vegas
