/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitCompletion
import Vegas.Source.CommitRecoveryNoMiss
import Interaction.ReactiveMenuRestriction

/-! # Surviving typed prefix observations with unfinished foreign bindings -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

/-- A surviving owner reads the same exact typed observation from the actual
accepted-table decoder and from the partial native store. Only its own earlier
slots must have completed; hidden unfinished foreign slots are allowed. -/
theorem decodeCommitAttempt_surviving_view_eq_fill
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (valid : native.BindingInvariant) (who : Player)
    (entry filler : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (sameEntry : entry.view who = filler.view who)
    (completed : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      eventOwner? (block.prepend suffix) index = some who →
        embedding.event index ∈ native.config.cut.completed)
    (survives : who ∉
      (decodeCommitAttempt whole mode block suffix embedding native entry excluded).2.1) :
    (decodeCommitAttempt whole mode block suffix embedding native entry excluded).1.view who =
      (fillCommitPrefix whole block suffix embedding native.config.store filler).view who := by
  induction block generalizing excluded with
  | nil => exact sameEntry
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let laterEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.ref zero
      let choice := (field.get? native.config.store).getD .failure
      have laterCompleted : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → eventOwner? (rest.prepend suffix) index = some who →
            laterEmbedding.event index ∈ native.config.cut.completed := by
        intro index inside owned
        exact completed (Fin.succ index) (by
          change index.val + 1 < rest.length + 1
          omega) owned
      by_cases inactive : owner ∈ excluded
      · have outside : owner ≠ who := by
          intro own
          have inherited := (decodeCommitAttempt whole mode
            (.commit name owner fresh guard rest) suffix embedding native entry
              excluded).2.2.excluded_subset
          exact survives (own ▸ inherited inactive)
        have extended : (automaticCommit name owner payload entry).view who =
            (commitSuccessor name guard filler choice).view who :=
          (SourceProgram.Config.automaticCommit_view_eq_failure who owner outside name guard
            entry).trans
            (SourceProgram.Config.view_commit_congr name guard entry filler sameEntry
              .failure choice (fun own => (outside own).elim))
        have laterActive : who ∉ (decodeCommitAttempt whole mode rest suffix laterEmbedding native
            (automaticCommit name owner payload entry) excluded).2.1 := by
          have actual := survives
          dsimp only [decodeCommitAttempt] at actual
          rw [dite_eq_left inactive] at actual
          exact actual
        have later := ih suffix laterEmbedding
          (automaticCommit name owner payload entry) (commitSuccessor name guard filler choice)
          excluded extended laterCompleted laterActive
        simpa [decodeCommitAttempt, inactive, fillCommitPrefix,
          zero, field, choice, laterEmbedding] using later
      · let result := (native.accepted (.inr (embedding.event zero))).elim
          PublicationResult.failure (fun candidate => native.bindingResult candidate payload)
        have same : owner = who → result = choice := by
          intro own
          have owned : eventOwner? ((CommitPrefix.commit name owner fresh guard rest).prepend
              suffix) zero = some who := by
            simpa only [CommitPrefix.prepend, eventOwner?, zero, Fin.mk_zero, Fin.cases_zero]
              using congrArg some own
          have present := completed zero (by
            simp only [zero, CommitPrefix.length]
            omega) owned
          have read := valid.binding_read field (embedding.event zero) rfl present
          have selected : choice = result := by
            dsimp only [choice]
            rw [read]
            rfl
          exact selected.symm
        have extended := SourceProgram.Config.view_commit_congr name guard entry filler sameEntry
          result choice same
        let after := excludeCommit excluded owner
          (native.accepted (.inr (embedding.event zero))).isNone
        have laterActive : who ∉ (decodeCommitAttempt whole mode rest suffix laterEmbedding native
            (commitSuccessor name guard entry result) after).2.1 := by
          have actual := survives
          dsimp only [decodeCommitAttempt] at actual
          rw [dite_eq_right inactive] at actual
          exact actual
        have later := ih suffix laterEmbedding
          (commitSuccessor name guard entry result) (commitSuccessor name guard filler choice)
          after extended laterCompleted laterActive
        simpa [decodeCommitAttempt, inactive, fillCommitPrefix,
          zero, field, choice, laterEmbedding, result, after] using later

end Vegas
