/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitAttemptOwnRecall

/-! # Exact retained action words of surviving commitment owners -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : ExecutionMode)

/-- A surviving owner retains every original binding choice in this attempt.
Other owners may already be excluded or become excluded inside the block. -/
theorem decodeCommitAttempt_history_of_surviving_owner
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) (who : Player)
    (survives : who ∉ (decodeCommitAttempt whole mode block suffix embedding native entry
      excluded).2.1)
    (actions : ∀ index action, decodeEventAction whole (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action)) :
    (decodeCommitAttempt whole mode block suffix embedding native entry excluded).1.history who =
      entry.history who ++ decodeHistory whole
        (commitAttemptCompletions whole mode block suffix embedding native) who := by
  induction block generalizing excluded with
  | nil => simp only [decodeCommitAttempt, commitAttemptCompletions, decodeHistory,
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
      let choice := (native.accepted (.inr event)).elim PublicationResult.failure
        (fun candidate => native.bindingResult candidate payload)
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
      have tailActions : ∀ index action,
          decodeEventAction whole (tailEmbedding.event index) action =
            decodeEventAction (rest.prepend suffix) index
              (cast (congrArg EventField.Action (tailEmbedding.layout_eq index)) action) := by
        intro index action
        have current := actions (Fin.succ index) action
        dsimp only [tailEmbedding]
        simpa only [CommitPrefix.prepend, decodeEventAction, Fin.cases_succ,
          OutputEmbedding.tail, Fin.cast_eq_self] using current
      have append (first second : List (toEventGraph whole).Completion) :
          decodeHistory whole (first ++ second) who =
            decodeHistory whole first who ++ decodeHistory whole second who := by
        simp only [decodeHistory, ownCompletions, List.filter_append, decodeCompletions_append]
      have firstHistory := decodeHistory_append_completion whole [] event action
      rw [decoded] at firstHistory
      have word : decodeHistory whole
          (commitAttemptCompletions whole mode
            (CommitPrefix.commit name owner fresh guard rest) suffix embedding native) who =
          (if who = owner then [OwnAction.commit owner name payload choice] else []) ++
            decodeHistory whole (commitAttemptCompletions whole mode rest suffix tailEmbedding
              native) who := by
        change decodeHistory whole ([⟨event, action⟩] ++ _) who = _
        rw [append]
        simp only [List.nil_append] at firstHistory
        rw [firstHistory]
        simp only [decodeHistory, ownCompletions, List.filter_nil, decodeCompletions,
          List.filterMap_nil, Function.update_apply, sourceActionOwner, List.nil_append]
        rfl
      by_cases inactive : owner ∈ excluded
      · have different : who ≠ owner := by
          intro same
          subst who
          exact survives ((decodeCommitAttempt whole mode
            (CommitPrefix.commit name owner fresh guard rest) suffix embedding native entry
              excluded).2.2.excluded_subset inactive)
        simp only [decodeCommitAttempt] at survives ⊢
        rw [dite_eq_left inactive] at survives ⊢
        rw [ih suffix tailEmbedding (automaticCommit name owner payload entry) excluded
          survives tailActions, word]
        simp only [automaticCommit, different, ↓reduceIte, List.nil_append]
      · simp only [decodeCommitAttempt] at survives ⊢
        rw [dite_eq_right inactive] at survives ⊢
        rw [ih suffix tailEmbedding (commitSuccessor name guard entry choice)
          (excludeCommit excluded owner (native.accepted (.inr event)).isNone)
          survives tailActions, word]
        by_cases same : who = owner
        · subst who
          simp only [commitSuccessor, Function.update_self, ↓reduceIte, List.append_assoc]
        · simp only [commitSuccessor, Function.update_of_ne same, same, ↓reduceIte,
            List.nil_append]

/-- At a completed physical interval, a surviving source owner's new word is
the actual native suffix. The saved source history may contain retired attempts. -/
theorem decodeCommitAttempt_history_extension_of_survivor
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (offset : Nat)
    (rank : ∀ index, (embedding.event index).val = offset + index.val)
    (entryNative native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) (who : Player)
    (survives : who ∉ (decodeCommitAttempt whole mode block suffix embedding native entry
      excluded).2.1)
    (valid : native.BindingInvariant) {inputs} (reachable : native.config.Reachable inputs)
    (retained : entryNative.config.history.IsPrefix native.config.history)
    (saved : entryNative.config.cut.IsPrefix offset)
    (finished : native.config.cut.IsPrefix (offset + block.length))
    (actions : ∀ index action, decodeEventAction whole (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action)) :
    (decodeCommitAttempt whole mode block suffix embedding native entry excluded).1.history who =
      entry.history who ++
        (decodeHistory whole (native.config.history.map
          ((toEventGraph whole).fromModeCompletion mode)) who).drop
            (decodeHistory whole (entryNative.config.history.map
              ((toEventGraph whole).fromModeCompletion mode)) who).length := by
  rw [decodeCommitAttempt_history_of_surviving_owner whole mode block suffix embedding native
    entry excluded who survives actions]
  have recall := commitAttemptCompletions_ownRecall whole mode block suffix embedding offset rank
    entryNative native valid reachable retained saved who
      (fun index inside _acting => (finished.2 _).mpr (by rw [rank]; omega))
      (fun event done _acting => (finished.2 event).mp done)
  have decoded := congrArg (fun past => decodeCompletions whole
    (past.map ((toEventGraph whole).fromModeCompletion mode))) recall
  have fromMode (past : List ((toEventGraph whole).withMode mode).Completion) :
      decodeHistory whole (past.map ((toEventGraph whole).fromModeCompletion mode)) who =
        decodeCompletions whole
          ((((toEventGraph whole).withMode mode).ownCompletions who past).map
            ((toEventGraph whole).fromModeCompletion mode)) := by
    simp only [decodeHistory, ownCompletions, List.filter_map]
    rfl
  rw [← fromMode, ← fromMode, List.map_append] at decoded
  have projected : ((commitAttemptCompletions whole mode block suffix embedding native).map
      ((toEventGraph whole).toModeCompletion mode)).map
        ((toEventGraph whole).fromModeCompletion mode) =
      commitAttemptCompletions whole mode block suffix embedding native := by
    rw [List.map_map]
    apply List.map_id''
    intro completion
    exact fromModeCompletion_toModeCompletion (toEventGraph whole) mode completion
  rw [projected] at decoded
  have append (first second : List (toEventGraph whole).Completion) :
      decodeHistory whole (first ++ second) who =
        decodeHistory whole first who ++ decodeHistory whole second who := by
    simp only [decodeHistory, ownCompletions, List.filter_append, decodeCompletions_append]
  rw [append] at decoded
  rw [decoded]
  simp only [List.drop_left]

end Vegas
