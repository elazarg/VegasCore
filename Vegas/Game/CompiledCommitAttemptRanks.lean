/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitAttemptSplit
import Vegas.Source.CommitAttemptRanks
import Vegas.Source.CommitPrefixPointAppend

/-! # Earlier observations of the exact physical commitment decoder -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

/-- The actual earlier physical decoder is recovered at its original source
rank from the same whole decoded attempt. Automatic exclusions, missing flags
and all prior original owned actions remain in the decoded configurations. -/
theorem decodeCommitAttempt_atRank
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append later).prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (who : Player)
    (survives : who ∉
      (decodeCommitAttempt whole mode (earlier.append later) suffix embedding native
        entry excluded).2.1) :
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole))
        (earlier.prepend_append later suffix)) embedding
    let middle := decodeCommitAttempt whole mode earlier (later.prepend suffix)
      prefixEmbedding native entry excluded
    let complete := decodeCommitAttempt whole mode (earlier.append later) suffix
      embedding native entry excluded
    ProtocolView.atRank who (earlier.prepend (later.prepend suffix)) earlier.length
        (ProtocolState.observe who (earlier.prepend (later.prepend suffix))
          (cast (congrArg ProtocolState (earlier.prepend_append later suffix))
            ((earlier.append later).liftPoint suffix (ProtocolState.entry suffix complete.1)))) =
      some (ProtocolState.observe who (earlier.prepend (later.prepend suffix))
        (earlier.liftPoint (later.prepend suffix)
          (ProtocolState.entry (later.prepend suffix) middle.1))) := by
  intro prefixEmbedding middle complete
  obtain ⟨attempt⟩ := decodeCommitAttempt_append_attempt whole mode earlier later suffix
    embedding native entry excluded
  rw [earlier.liftPoint_append later suffix]
  exact attempt.atRank_lift earlier suffix who survives

end Vegas
