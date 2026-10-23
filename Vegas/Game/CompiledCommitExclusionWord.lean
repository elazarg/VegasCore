/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledCommitAttempt
import Vegas.Source.CommitRecoveryInstructions
import Vegas.Pending.PhaseSavedExclusionReadback

/-! # Actual completed omission masks determine the entire source exclusion scan -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}

/-- The decoded omission scan is the actual public failure scan at every
original commitment rank. Accepted unusable values never create omissions. -/
theorem decodeCommitAttempt_exclusionWord_scan [Fintype Player]
    (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (offset : Nat)
    (ranked : ∀ index, (embedding.event index).val = offset + index.val)
    (completed : ∀ index, index.val < block.length →
      embedding.event index ∈ native.config.cut.completed)
    (entry : SourceProgram.Config Player L Γ) (excluded inherited : Finset Player)
    (before : excluded = inherited ∪ native.failureOwnersBefore offset) :
    CommitPrefix.Attempt.exclusionsAfter
        (decodeCommitAttempt whole mode block suffix embedding native entry excluded).2.2 =
      (List.range block.length).map (fun index =>
        inherited ∪ native.failureOwnersBefore (offset + index + 1)) := by
  classical
  induction block generalizing offset excluded with
  | nil => rfl
  | @commit Γ Δ O P name owner payload fresh guard rest ih =>
      let head : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let event := embedding.event head
      let tailEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have rank : event.val = offset := by simpa only [head, Nat.add_zero] using ranked head
      have layout : ((toEventGraph whole).withMode mode).outputLayout event =
          .binding owner payload := by
        exact embedding.layout_eq head
      have acting := EventGraph.actor?_of_outputLayout_binding
        ((toEventGraph whole).withMode mode) layout
      have omitted := native.publicFailure_iff_accepted_none event owner payload layout
        (completed head (by simp only [head, CommitPrefix.length]; omega))
      have update := native.union_failureOwnersBefore_successor event inherited
      rw [acting, Option.elim_some, rank, ← before] at update
      have tailRank : ∀ index, (tailEmbedding.event index).val = offset + 1 + index.val := by
        intro index
        dsimp only [tailEmbedding, OutputEmbedding.tail]
        rw [ranked]
        simp only [Fin.val_cast, Fin.val_succ]
        omega
      have tailCompleted : ∀ index, index.val < rest.length →
          tailEmbedding.event index ∈ native.config.cut.completed := by
        intro index bound
        apply completed
        simpa only [Fin.val_cast, Fin.val_succ, CommitPrefix.length] using
          Nat.succ_lt_succ bound
      have mapped : (List.range (rest.length + 1)).map (fun index =>
          inherited ∪ native.failureOwnersBefore (offset + index + 1)) =
          (inherited ∪ native.failureOwnersBefore (offset + 1)) ::
            (List.range rest.length).map (fun index =>
              inherited ∪ native.failureOwnersBefore (offset + 1 + index + 1)) := by
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
        congr 1
        apply List.map_congr_left
        intro index _
        congr 2
        omega
      by_cases inactive : owner ∈ excluded
      · rw [decodeCommitAttempt, dite_eq_left inactive]
        change excluded :: _ = _
        have headExcluded : inherited ∪ native.failureOwnersBefore (offset + 1) = excluded := by
          rw [update]
          split
          · exact Finset.insert_eq_of_mem inactive
          · rfl
        rw [CommitPrefix.length, mapped, headExcluded]
        congr 1
        exact ih suffix tailEmbedding (offset + 1) tailRank tailCompleted _ excluded
          headExcluded.symm
      · rw [decodeCommitAttempt, dite_eq_right inactive]
        dsimp only [CommitPrefix.Attempt.exclusionsAfter]
        have headExcluded : excludeCommit excluded owner
            (native.accepted (.inr event)).isNone =
              inherited ∪ native.failureOwnersBefore (offset + 1) := by
          rw [update]
          cases accepted : native.accepted (.inr event) with
          | none =>
              have failed := omitted.mpr accepted
              simp only [Option.isNone_none, excludeCommit, failed, ↓reduceIte]
          | some candidate =>
              have notFailed : ¬native.PublicFailure event := by
                intro failed
                rw [accepted] at omitted
                cases omitted.mp failed
              simp only [Option.isNone_some, excludeCommit, notFailed,
                Bool.false_eq_true, ↓reduceIte]
        rw [CommitPrefix.length, mapped, headExcluded]
        congr 1
        exact ih suffix tailEmbedding (offset + 1) tailRank tailCompleted _
          (inherited ∪ native.failureOwnersBefore (offset + 1)) rfl

end Vegas
