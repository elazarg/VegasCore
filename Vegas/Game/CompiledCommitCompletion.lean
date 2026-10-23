/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledCommitState
import Vegas.Compile.CommitPrefixCompletion
import Interaction.ReactiveMenuRestriction

/-! # Exact source completion of a clear decoded physical commitment attempt -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

/-- A real decoded attempt ending without exclusions is exactly the source
completion read from its physical fields, including registry and full own words.
Its actual monotone exclusion record discharges all automatic/missing branches. -/
theorem decodeCommitAttempt_eq_fill_of_clear
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (valid : native.BindingInvariant) (entry : SourceProgram.Config Player L Γ)
    (excluded : Finset Player)
    (completed : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      embedding.event index ∈ native.config.cut.completed)
    (clear : (decodeCommitAttempt whole mode block suffix embedding native entry excluded).2.1 =
      ∅) :
    (decodeCommitAttempt whole mode block suffix embedding native entry excluded).1 =
      fillCommitPrefix whole block suffix embedding native.config.store entry := by
  induction block generalizing excluded with
  | nil => rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      have inherited := (decodeCommitAttempt whole mode
        (CommitPrefix.commit name owner fresh guard rest) suffix embedding native entry
          excluded).2.2.excluded_subset
      rw [clear] at inherited
      have empty : excluded = ∅ := Finset.subset_empty.mp inherited
      subst excluded
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let laterEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have output : ((toEventGraph whole).withMode mode).outputLayout (embedding.event zero) =
          .binding owner payload := by
        change outputLayout whole (embedding.event zero) = .binding owner payload
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.layout_eq zero
      let field : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (embedding.event zero), output⟩
      let choice := (native.accepted (.inr (embedding.event zero))).elim
        PublicationResult.failure (fun candidate => native.bindingResult candidate payload)
      have read := valid.binding_read field (embedding.event zero) rfl
        (completed zero (by simp only [zero, CommitPrefix.length]; omega))
      have selected : (field.get? native.config.store).getD .failure = choice := by
        rw [read]
        rfl
      have laterCompleted : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → laterEmbedding.event index ∈ native.config.cut.completed := by
        intro index inside
        exact completed (Fin.succ index) (by
          change index.val + 1 < rest.length + 1
          omega)
      let next := commitSuccessor name guard entry choice
      let laterExcluded := excludeCommit ∅ owner
        (native.accepted (.inr (embedding.event zero))).isNone
      have laterClear : (decodeCommitAttempt whole mode rest suffix laterEmbedding native next
          laterExcluded).2.1 = ∅ := by
        simpa [decodeCommitAttempt, laterEmbedding, next, choice, laterExcluded, zero] using clear
      have later := ih suffix laterEmbedding next laterExcluded laterCompleted laterClear
      change (decodeCommitAttempt whole mode rest suffix laterEmbedding native next
          laterExcluded).1 = fillCommitPrefix whole rest suffix laterEmbedding
        native.config.store (commitSuccessor name guard entry
          ((field.get? native.config.store).getD .failure))
      rw [selected]
      exact later

end Vegas
