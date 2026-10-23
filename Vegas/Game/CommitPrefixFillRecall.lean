/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.CommitPrefixCompletion
import Vegas.Game.CommitAttemptHistory
import Vegas.Pending.EventBindingReadback
import Interaction.ReactiveMenuRestriction

/-! # Effective own actions of a source completion of hidden bindings -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

private theorem fill_decodeHistory_append
    (first second : List (toEventGraph whole).Completion) (who : Player) :
    decodeHistory whole (first ++ second) who =
      decodeHistory whole first who ++ decodeHistory whole second who := by
  simp only [decodeHistory, ownCompletions, List.filter_append, decodeCompletions_append]

/-- Completing hidden foreign cells changes no remembered action of this
owner. Only this owner's earlier slots need be physically complete; foreign
holes may remain, and accepted unusable meanings are retained exactly. -/
theorem fillCommitPrefix_history
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (valid : native.BindingInvariant)
    (who : Player)
    (completed : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      ((toEventGraph whole).withMode mode).actor? (embedding.event index) = some who →
        embedding.event index ∈ native.config.cut.completed)
    (actions : ∀ index action, decodeEventAction whole (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action)) :
    (fillCommitPrefix whole block suffix embedding native.config.store entry).history who =
      entry.history who ++
        decodeHistory whole (commitAttemptCompletions whole mode block suffix embedding native)
          who := by
  induction block with
  | nil => simp only [fillCommitPrefix, commitAttemptCompletions, decodeHistory, ownCompletions,
      List.filter_nil, decodeCompletions, List.filterMap_nil, List.append_nil]
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let event := embedding.event zero
      let binding : outputLayout whole event = .binding owner payload := by
        simpa only [zero, event, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.layout_eq zero
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.ref zero
      let choice := (field.get? native.config.store).getD .failure
      let actual := (native.accepted (.inr event)).elim PublicationResult.failure
        (fun candidate => native.bindingResult candidate payload)
      let action : (toEventGraph whole).Action event :=
        cast (congrArg EventField.Action binding.symm) actual
      let laterEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have headChoice : owner = who → choice = actual := by
        intro same
        have acting : ((toEventGraph whole).withMode mode).actor? event = some who := by
          rw [EventGraph.actor?_of_outputLayout_binding _ binding, same]
        have done := completed zero (by
          simp only [zero, SourceProgram.CommitPrefix.length]; omega) acting
        have present : (field.get? native.config.store).isSome = true := by
          apply field.get?_isSome
          change (native.config.store (.inr event)).isSome = true
          rw [EventGraph.Config.store_output, native.config.output_available]
          exact done
        obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
        have meaning := valid.binding_value field value stored
        change value = actual at meaning
        simp only [choice, stored, Option.getD_some]
        exact meaning
      have decoded : decodeEventAction whole event action =
          some (.commit owner name payload actual) := by
        have encoded := actions zero action
        have returned : cast (congrArg EventField.Action (embedding.layout_eq zero)) action =
            actual := by
          simp only [action, cast_cast, cast_eq]
        rw [returned] at encoded
        change decodeEventAction whole (embedding.event zero) action = _
        simpa only [SourceProgram.CommitPrefix.prepend, decodeEventAction, zero, Fin.mk_zero,
          Fin.cases_zero] using encoded
      have tailCompleted : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length →
          ((toEventGraph whole).withMode mode).actor? (laterEmbedding.event index) = some who →
            laterEmbedding.event index ∈ native.config.cut.completed := by
        intro index before acting
        exact completed (Fin.succ index)
          (by change index.val + 1 < rest.length + 1; omega) acting
      have tailActions : ∀ index action,
          decodeEventAction whole (laterEmbedding.event index) action =
            decodeEventAction (rest.prepend suffix) index
              (cast (congrArg EventField.Action (laterEmbedding.layout_eq index)) action) := by
        intro index action
        have current := actions (Fin.succ index) action
        dsimp only [laterEmbedding]
        simpa only [SourceProgram.CommitPrefix.prepend, decodeEventAction, Fin.cases_succ,
          OutputEmbedding.tail, Fin.cast_eq_self] using current
      have later := ih suffix laterEmbedding (commitSuccessor name guard entry choice)
        tailCompleted tailActions
      have firstHistory := decodeHistory_append_completion whole [] event action
      rw [decoded] at firstHistory
      have word : decodeHistory whole
          (commitAttemptCompletions whole mode
            (SourceProgram.CommitPrefix.commit name owner fresh guard rest) suffix embedding
              native) who =
          (if who = owner then [OwnAction.commit owner name payload actual] else []) ++
            decodeHistory whole (commitAttemptCompletions whole mode rest suffix laterEmbedding
              native) who := by
        change decodeHistory whole (⟨event, action⟩ :: _) who = _
        change decodeHistory whole ([⟨event, action⟩] ++ _) who = _
        rw [fill_decodeHistory_append]
        simp only [List.nil_append] at firstHistory
        rw [firstHistory]
        simp only [decodeHistory, ownCompletions, List.filter_nil, decodeCompletions,
          List.filterMap_nil, Function.update_apply, sourceActionOwner, List.nil_append]
        rfl
      change (fillCommitPrefix whole rest suffix laterEmbedding native.config.store
        (commitSuccessor name guard entry choice)).history who = _
      rw [later, word]
      by_cases same : who = owner
      · subst who
        rw [headChoice rfl]
        simp only [commitSuccessor, Function.update_self, ↓reduceIte, List.append_assoc]
      · simp only [commitSuccessor, Function.update_of_ne same, same, ↓reduceIte, List.nil_append]

end Vegas
