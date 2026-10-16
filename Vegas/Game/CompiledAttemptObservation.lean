/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitState
import Vegas.Source.CommitBlockInformation

/-! # Owned source prefix observations read from the actual accepted tables -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

private theorem own_binding_result_eq {graph : Vegas.EventGraph Player L}
    (first second : EventGraphRuntime.State graph)
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload)
    (firstCompleted : event ∈ first.config.cut.completed)
    (secondCompleted : event ∈ second.config.cut.completed)
    (observed : graph.playerObserve who first.config = graph.playerObserve who second.config) :
    (first.accepted (.inr event)).elim .failure
        (fun candidate => first.bindingResult candidate payload) =
      (second.accepted (.inr event)).elim .failure
        (fun candidate => second.bindingResult candidate payload) := by
  let ref : FieldRef graph.layout (.binding who payload) := ⟨.inr event, binding⟩
  have visible : (EventField.binding who payload).VisibleTo who := rfl
  have masks := congrArg (fun view : graph.PlayerObservation who => view.store) observed
  have values : ref.get? first.config.store = ref.get? second.config.store := by
    exact (ref.get?_playerStore who first.config.store visible).symm.trans
      ((congrArg ref.get? masks).trans (ref.get?_playerStore who second.config.store visible))
  exact Option.some.inj ((firstValid.binding_read ref event rfl firstCompleted).symm.trans
    (values.trans (secondValid.binding_read ref event rfl secondCompleted)))

/-- The same authentic public table and owner-masked observation determine
every decoded commitment-prefix view and processed exclusion set. Hidden
foreign accepted results may differ, including accepted failed results. -/
theorem decodeCommitAttempt_view_eq {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (first second : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (who : Player) (firstEntry secondEntry : SourceProgram.Config Player L Γ)
    (excluded : Finset Player) (entry : firstEntry.view who = secondEntry.view who)
    (publicView : first.publicView = second.publicView)
    (observed : ((toEventGraph whole).withMode mode).playerObserve who first.config =
      ((toEventGraph whole).withMode mode).playerObserve who second.config)
    (firstCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → embedding.event index ∈ first.config.cut.completed)
    (secondCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → embedding.event index ∈ second.config.cut.completed) :
    (decodeCommitAttempt whole mode block suffix embedding first firstEntry excluded).1.view who =
        (decodeCommitAttempt whole mode block suffix embedding second secondEntry excluded).1.view
          who ∧
      (decodeCommitAttempt whole mode block suffix embedding first firstEntry excluded).2.1 =
        (decodeCommitAttempt whole mode block suffix embedding second
          secondEntry excluded).2.1 := by
  have accepted : first.accepted = second.accepted := congrArg PublicView.accepted publicView
  induction block generalizing excluded with
  | nil => exact ⟨entry, rfl⟩
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let event := embedding.event zero
      let laterEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have output : ((toEventGraph whole).withMode mode).outputLayout event =
          .binding owner payload := by
        change outputLayout whole event = .binding owner payload
        simpa only [event, zero, SourceProgram.CommitPrefix.prepend, outputLayout,
          Fin.mk_zero, Fin.cases_zero] using embedding.layout_eq zero
      have leftCompleted : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → laterEmbedding.event index ∈ first.config.cut.completed := by
        intro index inside
        exact firstCompleted (Fin.succ index) (by
          change index.val + 1 < rest.length + 1
          omega)
      have rightCompleted : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → laterEmbedding.event index ∈ second.config.cut.completed := by
        intro index inside
        exact secondCompleted (Fin.succ index) (by
          change index.val + 1 < rest.length + 1
          omega)
      by_cases inactive : owner ∈ excluded
      · have extended : (automaticCommit name owner payload firstEntry).view who =
            (automaticCommit name owner payload secondEntry).view who := by
          apply Prod.ext
          · simpa only [SourceProgram.Config.view, automaticCommit, commitSuccessor] using
              congrArg Prod.fst
                (SourceProgram.Config.view_commit_congr name guard firstEntry secondEntry entry
                  .failure .failure (fun _ => rfl))
          · change firstEntry.history who = secondEntry.history who
            exact congrArg Prod.snd entry
        have later := ih suffix laterEmbedding (automaticCommit name owner payload firstEntry)
          (automaticCommit name owner payload secondEntry) excluded extended leftCompleted
          rightCompleted
        constructor
        · simpa only [decodeCommitAttempt, inactive, ↓reduceDIte, ↓reduceIte, laterEmbedding,
            zero, event] using later.1
        · dsimp only [decodeCommitAttempt]
          rw [dite_eq_left inactive, dite_eq_left inactive]
          exact later.2
      · let left := (first.accepted (.inr event)).elim PublicationResult.failure
          (fun candidate => first.bindingResult candidate payload)
        let right := (second.accepted (.inr event)).elim PublicationResult.failure
          (fun candidate => second.bindingResult candidate payload)
        have result : owner = who → left = right := by
          intro own
          subst owner
          exact own_binding_result_eq first second firstValid secondValid who event payload output
            (firstCompleted zero (by simp only [zero, SourceProgram.CommitPrefix.length]; omega))
            (secondCompleted zero (by simp only [zero, SourceProgram.CommitPrefix.length]; omega))
            observed
        have extended := SourceProgram.Config.view_commit_congr name guard firstEntry secondEntry
          entry left right result
        have sameMiss : (second.accepted (.inr event)).isNone =
            (first.accepted (.inr event)).isNone :=
          congrArg Option.isNone (congrFun accepted (.inr event)).symm
        dsimp only [event, zero] at sameMiss
        have later := ih suffix laterEmbedding (commitSuccessor name guard firstEntry left)
          (commitSuccessor name guard secondEntry right)
          (excludeCommit excluded owner (first.accepted (.inr event)).isNone) extended
          leftCompleted rightCompleted
        constructor
        · dsimp only [decodeCommitAttempt]
          rw [dite_eq_right inactive, dite_eq_right inactive]
          dsimp only
          rw [sameMiss]
          exact later.1
        · dsimp only [decodeCommitAttempt]
          rw [dite_eq_right inactive, dite_eq_right inactive]
          dsimp only
          rw [sameMiss]
          exact later.2

end Vegas
