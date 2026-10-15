/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitAttempt
import Vegas.Compile.EventGraphPolicyLaw

/-! # Exact original action words read from clear commitment attempts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : ExecutionMode)

/-- Source-ranked records of the immutable accepted binding meanings. -/
def commitAttemptCompletions : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : CommitPrefix Γ O Δ P) → (suffix : SourceProgram Player L Δ P) →
    OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (block.prepend suffix) →
    EventGraphRuntime.State ((toEventGraph whole).withMode mode) →
    List (toEventGraph whole).Completion
  | _, _, _, _, .nil, _, _, _ => []
  | _, _, _, _, .commit name owner fresh guard rest, suffix, embedding, native =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let event := embedding.event zero
      let binding : outputLayout whole event = .binding owner _ := by
        simpa only [zero, event, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero]
          using embedding.layout_eq zero
      let choice := (native.accepted (.inr event)).elim PublicationResult.failure
        (fun candidate => native.bindingResult candidate _)
      let action := cast (congrArg EventField.Action binding.symm) choice
      let later := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      ⟨event, action⟩ :: commitAttemptCompletions rest suffix later native

private theorem decodeHistory_append
    (first second : List (toEventGraph whole).Completion) (who : Player) :
    decodeHistory whole (first ++ second) who =
      decodeHistory whole first who ++ decodeHistory whole second who := by
  simp only [decodeHistory, ownCompletions, List.filter_append, decodeCompletions_append]

/-- The source telescope appends the exact accepted action word. The compiler
lookup certificate retains original variable names, rather than just event IDs. -/
theorem decodeCommitAttempt_history_of_accepted
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ)
    (accepted : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      native.accepted (.inr (embedding.event index)) ≠ none)
    (actions : ∀ index action, decodeEventAction whole (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action)) :
    ∀ who, (decodeCommitAttempt whole mode block suffix embedding native entry ∅).1.history who =
      entry.history who ++
        decodeHistory whole (commitAttemptCompletions whole mode block suffix embedding native)
          who := by
  induction block with
  | nil => intro who; simp only [decodeCommitAttempt, commitAttemptCompletions, decodeHistory,
      ownCompletions, List.filter_nil, decodeCompletions, List.filterMap_nil, List.append_nil]
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let event := embedding.event zero
      let binding : outputLayout whole event = .binding owner payload := by
        simpa only [zero, event, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero]
          using embedding.layout_eq zero
      let tailEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have nonempty := accepted zero (by simp only [zero, CommitPrefix.length]; omega)
      obtain ⟨candidate, found⟩ := Option.ne_none_iff_exists'.mp nonempty
      let choice := native.bindingResult candidate payload
      let action : (toEventGraph whole).Action event :=
        cast (congrArg EventField.Action binding.symm) choice
      have decoded : decodeEventAction whole event action =
          some (.commit owner name payload choice) := by
        have encoded := actions zero action
        have returned : cast (congrArg EventField.Action (embedding.layout_eq zero)) action =
            choice := by
          simp only [action, cast_cast, cast_eq]
        rw [returned] at encoded
        change decodeEventAction whole (embedding.event zero) action = _
        simpa only [CommitPrefix.prepend, decodeEventAction, zero, Fin.mk_zero, Fin.cases_zero]
          using encoded
      have tailAccepted : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → native.accepted (.inr (tailEmbedding.event index)) ≠ none := by
        intro index before
        exact accepted (Fin.succ index) (by change index.val + 1 < rest.length + 1; omega)
      have tailActions : ∀ index action,
          decodeEventAction whole (tailEmbedding.event index) action =
            decodeEventAction (rest.prepend suffix) index
              (cast (congrArg EventField.Action (tailEmbedding.layout_eq index)) action) := by
        intro index action
        have current := actions (Fin.succ index) action
        dsimp only [tailEmbedding]
        simpa only [CommitPrefix.prepend, decodeEventAction, Fin.cases_succ,
          OutputEmbedding.tail, Fin.cast_eq_self] using current
      have later := ih suffix tailEmbedding (commitSuccessor name guard entry choice)
        tailAccepted tailActions
      intro who
      have firstHistory := decodeHistory_append_completion whole [] event action
      rw [decoded] at firstHistory
      have word : decodeHistory whole
          (commitAttemptCompletions whole mode
            (CommitPrefix.commit name owner fresh guard rest) suffix embedding native) who =
          (if who = owner then [OwnAction.commit owner name payload choice] else []) ++
            decodeHistory whole (commitAttemptCompletions whole mode rest suffix tailEmbedding
              native) who := by
        dsimp only [commitAttemptCompletions]
        change decodeHistory whole (⟨event,
          cast (congrArg EventField.Action binding.symm)
            ((native.accepted (.inr event)).elim .failure
              (fun candidate => native.bindingResult candidate payload))⟩ :: _) who = _
        rw [found]
        change decodeHistory whole (⟨event, action⟩ :: _) who = _
        change decodeHistory whole ([⟨event, action⟩] ++ _) who = _
        rw [decodeHistory_append]
        simp only [List.nil_append] at firstHistory
        rw [firstHistory]
        simp only [decodeHistory, ownCompletions, List.filter_nil, decodeCompletions,
          List.filterMap_nil, Function.update_apply, sourceActionOwner, List.nil_append]
        rfl
      have continuation :
          (decodeCommitAttempt whole mode (CommitPrefix.commit name owner fresh guard rest)
            suffix embedding native entry ∅).1 =
          (decodeCommitAttempt whole mode rest suffix tailEmbedding native
            (commitSuccessor name guard entry choice) ∅).1 := by
        simp only [decodeCommitAttempt, Finset.notMem_empty, ↓reduceDIte]
        change (decodeCommitAttempt whole mode rest suffix tailEmbedding native
          (commitSuccessor name guard entry ((native.accepted (.inr event)).elim .failure
            (fun candidate => native.bindingResult candidate payload)))
          (excludeCommit ∅ owner (native.accepted (.inr event)).isNone)).1 = _
        rw [found]
        rfl
      rw [continuation]
      rw [later, word]
      by_cases same : who = owner
      · subst who
        simp only [commitSuccessor, Function.update_self, ↓reduceIte,
          List.append_assoc]
      · simp only [commitSuccessor, Function.update_of_ne same, same,
          ↓reduceIte, List.nil_append]

end Vegas
