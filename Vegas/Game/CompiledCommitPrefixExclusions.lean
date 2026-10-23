/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledAttemptExclusion

/-! # Source-ordered exclusion signals from actual commitment receipts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

variable [Fintype Player]

open Classical in
/-- Public failure in the processed static commitment prefix is precisely
absence of its accepted receipt. Unprocessed later expiries are outside this
interval, and accepted unusable values are not counted as missing receipts. -/
theorem commitMissingOwners_eq_public_failures
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (offset : Nat)
    (ranks : ∀ index, (embedding.event index).val = offset + index.val)
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (completed : ∀ index, index.val < block.length →
      embedding.event index ∈ native.config.cut.completed) :
    commitMissingOwners whole mode block suffix embedding native =
      Finset.univ.filter (fun who => ∃ event : ((toEventGraph whole).withMode mode).EventId,
        offset ≤ event.val ∧ event.val < offset + block.length ∧
          ((toEventGraph whole).withMode mode).actor? event = some who ∧
            native.PublicFailure event) := by
  classical
  have bindingFailure : ∀ (index : Fin (eventCount (block.prepend suffix))),
      index.val < block.length →
        (native.PublicFailure (embedding.event index) ↔
          native.accepted (.inr (embedding.event index)) = none) := by
    intro index inside
    obtain ⟨owner, payload, _member, layout⟩ := block.binding_before_length suffix index inside
    have output : ((toEventGraph whole).withMode mode).outputLayout (embedding.event index) =
        .binding owner payload := (embedding.layout_eq index).trans layout
    have noPublication : RecoveryState.publicationFailed native (embedding.event index) =
        false := by
      cases view : nodeView ((toEventGraph whole).withMode mode) (embedding.event index) with
      | bind => simp only [RecoveryState.publicationFailed, view]
      | resolve author ty ref checks layout code => cases output.symm.trans layout
      | sample ty law layout code => cases output.symm.trans layout
    rw [State.PublicFailure, noPublication, Bool.false_eq_true, or_false,
      native.publicView_missedBinding _ owner payload output]
    exact and_iff_right (completed index inside)
  ext who
  rw [mem_commitMissingOwners]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨index, inside, acting, missing⟩
    refine ⟨embedding.event index, ?_, ?_, acting, (bindingFailure index inside).mpr missing⟩
    · rw [ranks]; omega
    · rw [ranks]; omega
  · rintro ⟨event, lower, upper, acting, failed⟩
    have counted := block.eventCount_prepend suffix
    let index : Fin (eventCount (block.prepend suffix)) := ⟨event.val - offset, by omega⟩
    have inside : index.val < block.length := by dsimp only [index]; omega
    have address : embedding.event index = event := by
      apply Fin.ext
      rw [ranks]
      dsimp only [index]
      omega
    exact ⟨index, inside, address.symm ▸ acting,
      (bindingFailure index inside).mp (address.symm ▸ failed)⟩

open Classical in
/-- The exclusion signal after scanning an actual source prefix is its saved
exclusion set union public failures inside that prefix, rather than the full
physical live exclusion set. -/
theorem decodeCommitAttempt_excluded_eq_public_prefix
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (offset : Nat)
    (ranks : ∀ index, (embedding.event index).val = offset + index.val)
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (completed : ∀ index, index.val < block.length →
      embedding.event index ∈ native.config.cut.completed)
    (entry : Config Player L Γ) (excluded : Finset Player) :
    (decodeCommitAttempt whole mode block suffix embedding native entry excluded).2.1 =
      excluded ∪ Finset.univ.filter (fun who =>
        ∃ event : ((toEventGraph whole).withMode mode).EventId,
          offset ≤ event.val ∧ event.val < offset + block.length ∧
            ((toEventGraph whole).withMode mode).actor? event = some who ∧
              native.PublicFailure event) := by
  rw [decodeCommitAttempt_excluded_eq,
    commitMissingOwners_eq_public_failures whole mode block suffix embedding offset ranks
      native completed]

end Vegas
