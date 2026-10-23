/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryFrontier
import Vegas.Source.CommitPrefixSplitting
import GameTheory.Protocol.ActionRestriction

/-! # Nonomitting source play stays clear through its commitment window -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitPrefix

/-- Every typed initial commitment segment fits inside the actual maximal
commitment window, even if its remaining suffix starts with more bindings. -/
theorem length_le_commit_window {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (entry : Config Player L Γ) :
    block.length + ProtocolState.commitEnd (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) entry) ≤
      ProtocolState.remaining (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) entry) := by
  have endpoint : ProtocolState.commitEnd (block.prepend suffix)
      (ProtocolState.entry (block.prepend suffix) entry) ≤ instructionCount suffix := by
    simp only [ProtocolState.commitEnd_entry]
    induction block with
    | nil =>
        simpa only [prepend, ProtocolState.commitEnd_entry, ProtocolState.remaining_entry] using
          ProtocolState.commitEnd_le_remaining suffix (ProtocolState.entry suffix entry)
    | commit name owner fresh guard rest ih =>
        exact ih suffix (automaticCommit name owner _ entry)
  rw [ProtocolState.remaining_entry, instructionCount_prepend]
  omega

end CommitPrefix
end Vegas.SourceProgram
