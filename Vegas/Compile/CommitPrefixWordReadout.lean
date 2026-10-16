/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixCompletion
import Vegas.Source.CommitPrefixAttemptReadout
import Vegas.Source.CommitPrefixWord

/-! # Original owned word actions read directly from the actual partial store -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

theorem compiledCommitPrefix_wordAction_none_of_unowned (block : CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P) (who : Player)
      (index : Fin (eventCount (block.prepend suffix))),
      eventOwner? (block.prepend suffix) index ≠ some who →
      ∀ word : DecisionView who Δ, block.wordAction who index.val word = none := by
  induction block with
  | nil => intro suffix who index _unowned word; rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
    intro suffix who index
    refine Fin.cases ?_ ?_ index
    · intro unowned word
      change some owner ≠ some who at unowned
      have different : owner ≠ who := fun same => unowned (congrArg some same)
      simp only [CommitPrefix.wordAction, Fin.val_zero, ite_eq_right different]
    · intro tail unowned word
      exact ih suffix who tail unowned word

/-- Filling the actual partial store reads exactly its original owned source
binding actions. Unavailable foreign cells may remain failed, and no source
support or intendedness premise is required. -/
theorem fillCommitPrefix_wordAction (block : CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        (block.prepend suffix))
      (_actions : ∀ index action, decodeEventAction whole (embedding.event index) action =
        decodeEventAction (block.prepend suffix) index
          (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
      (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ) (who : Player)
      (index : Fin (eventCount (block.prepend suffix))), index.val < block.length →
      ∀ (payload : L.Ty)
        (layout : outputLayout whole (embedding.event index) = .binding who payload),
        block.wordAction who index.val
            ((fillCommitPrefix whole block suffix embedding store entry).view who) =
          decodeEventAction whole (embedding.event index)
            (cast (congrArg EventField.Action layout.symm)
              (((⟨.inr (embedding.event index), layout⟩ :
                FieldRef (graphLayout whole) (.binding who payload)).get? store).getD
                  .failure)) := by
  induction block with
  | nil =>
    intro suffix embedding actions store entry who index impossible
    simp only [CommitPrefix.length] at impossible
    omega
  | @commit Γ O Δ P name owner value fresh guard rest ih =>
    intro suffix embedding actions store entry who index
    refine Fin.cases ?_ ?_ index
    · intro _inside payload layout
      have same : EventField.binding owner value = .binding who payload := by
        simpa only [CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          (embedding.layout_eq
            ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩).symm.trans layout
      cases same
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner value) := ⟨.inr _, layout⟩
      let result := (field.get? store).getD .failure
      let later := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let next := commitSuccessor name guard entry result
      have projected := CommitPrefix.Attempt.entryView_eq rest next _
        (fillCommitPrefix_attempt whole rest suffix later store next) owner
      have cell : (((rest.entryView owner
          ((fillCommitPrefix whole rest suffix later store next).view owner)).1.cells name
            (.commitment owner value) .here).getD .failure) = result := by
        rw [projected]
        simp only [next, commitSuccessor, Config.view, sourceObserve_commitment, ite_true,
          Option.getD_some]
        rfl
      let native : EventField.Action (outputLayout whole (embedding.event zero)) :=
        cast (congrArg EventField.Action layout.symm) result
      have decoded := actions zero native
      have returned : cast (congrArg EventField.Action (embedding.layout_eq zero)) native =
          result := by simp only [native, cast_cast, cast_eq]
      rw [returned] at decoded
      have exactAction : decodeEventAction whole (embedding.event zero) native =
          some (.commit owner name value result) := by
        simpa only [zero, CommitPrefix.prepend, decodeEventAction, Fin.mk_zero, Fin.cases_zero]
          using decoded
      simp only [CommitPrefix.wordAction, Fin.val_zero, ite_true, fillCommitPrefix]
      change some (OwnAction.commit owner name value
        (((rest.entryView owner ((fillCommitPrefix whole rest suffix later store next).view
          owner)).1.cells name (.commitment owner value) .here).getD .failure)) = _
      rw [cell]
      exact exactAction.symm
    · intro tail inside payload layout
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner value) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero]
          using embedding.ref zero
      let later := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have tailActions : ∀ index action,
          decodeEventAction whole (later.event index) action =
            decodeEventAction (rest.prepend suffix) index
              (cast (congrArg EventField.Action (later.layout_eq index)) action) := by
        intro index action
        have current := actions (Fin.succ index) action
        simpa only [later, CommitPrefix.prepend, decodeEventAction, Fin.cases_succ,
          OutputEmbedding.tail, Fin.cast_eq_self] using current
      exact ih suffix later tailActions store
        (commitSuccessor name guard entry ((field.get? store).getD .failure)) who tail
          (by change tail.val + 1 < rest.length + 1 at inside; omega) payload layout

end Vegas
