/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockPath
import Vegas.Source.CommitPrefixSplitting

/-! # Legal source recovery paths inside an unfinished commitment block -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An initial typed attempt strictly before the saved maximal endpoint is
reachable without closing or replacing that saved checkpoint. Empty initial
segments are included. -/
theorem Attempt.reaches_unclosed_lift
    {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (initial : Config Player L wholeΓ)
    {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ} {excluded : Finset Player}
    {finished : Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after)
    (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState whole)
    (ranks : ∀ point, ProtocolState.remaining whole (lift point) =
      ProtocolState.remaining (block.prepend suffix) point)
    (actors : ∀ point, ProtocolState.actor whole (lift point) =
      ProtocolState.actor (block.prepend suffix) point)
    (menus : ∀ point who, ProtocolView.recoveryAvailable who whole
      (ProtocolState.observe who whole (lift point)) =
      ProtocolView.recoveryAvailable who (block.prepend suffix)
        (ProtocolState.observe who (block.prepend suffix) point))
    (steps : ∀ point owners joint, ProtocolState.recoveryStep whole (lift point) owners joint =
      (ProtocolState.recoveryStep (block.prepend suffix) point owners joint).map
        (fun result => (lift result.1, result.2)))
    (state : CommitRecoveryState whole)
    (atEntry : state.point = lift (ProtocolState.entry (block.prepend suffix) entry))
    (stateExcluded : state.excluded = excluded)
    (committing : ProtocolState.atCommit whole state.saved = true)
    (beforeEnd : ProtocolState.commitEnd whole state.saved < instructionCount suffix) :
    (commitRecoveryProtocol whole initial).Reaches state
      (state.install (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), after)
        (fun _ member => attempt.excluded_subset (stateExcluded ▸ member))) := by
  by_cases positive : 0 < block.length
  · have path := attempt.instructions_closed_lift whole initial suffix lift ranks actors menus steps
      state atEntry stateExcluded committing beforeEnd.le positive
    have unfinished : ProtocolState.commitEnd whole state.saved <
        ProtocolState.remaining whole
          (lift (block.liftPoint suffix (ProtocolState.entry suffix finished))) := by
      rw [ranks, liftPoint_remaining, ProtocolState.remaining_entry]
      exact beforeEnd
    let next := state.install
      (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), after)
      (fun _ member => attempt.excluded_subset (stateExcluded ▸ member))
    rw [next.close_eq_self_of_remaining_gt committing unfinished] at path
    exact path.reaches
  · have zero : block.length = 0 := by omega
    obtain ⟨point, owners⟩ := attempt.liftPoint_entry_of_length_zero suffix zero
    have same : (state.install
        (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), after)
        (fun _ member => attempt.excluded_subset (stateExcluded ▸ member))) = state := by
      simp only [point, owners, CommitRecoveryState.install, ← atEntry, ← stateExcluded]
    rw [same]
    exact .refl _

end Vegas.SourceProgram.CommitPrefix
