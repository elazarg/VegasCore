/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitAttemptHistory
import Vegas.Pending.RecordedBindingReadback
import Vegas.EventGraph.RelaxedRecall
import Vegas.EventGraph.SequentialLaw

/-! # Typed binding records identify the complete original own action word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : ExecutionMode)

theorem commitAttemptCompletions_event_mem
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (event : (toEventGraph whole).EventId) :
    event ∈ (commitAttemptCompletions whole mode block suffix embedding native).map
        Completion.event ↔
      ∃ index : Fin (eventCount (block.prepend suffix)),
        index.val < block.length ∧ embedding.event index = event := by
  induction block with
  | nil => simp only [commitAttemptCompletions, List.map_nil, List.not_mem_nil,
      CommitPrefix.length, Nat.not_lt_zero, false_and, exists_false]
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let later := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      change event ∈ embedding.event zero ::
        (commitAttemptCompletions whole mode rest suffix later native).map Completion.event ↔ _
      rw [List.mem_cons, ih]
      constructor
      · rintro (same | ⟨index, inside, same⟩)
        · exact ⟨zero, by simp only [zero, CommitPrefix.length]; omega, same.symm⟩
        · exact ⟨Fin.succ index, by change index.val + 1 < rest.length + 1; omega,
            (show embedding.event (Fin.succ index) = later.event index from rfl).trans same⟩
      · rintro ⟨index, inside, same⟩
        revert inside same
        refine Fin.cases ?_ ?_ index
        · intro _ same
          exact Or.inl same.symm
        · intro index inside same
          right
          refine ⟨index, by change index.val + 1 < rest.length + 1 at inside; omega, ?_⟩
          simpa only [later, OutputEmbedding.tail, Fin.cast_eq_self] using same

theorem commitAttemptCompletions_pairwise
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode)) :
    ((commitAttemptCompletions whole mode block suffix embedding native).map
      Completion.event).Pairwise (fun left right => left.val < right.val) := by
  induction block with
  | nil => exact List.Pairwise.nil
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let later := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      change List.Pairwise _ (embedding.event zero ::
        (commitAttemptCompletions whole mode rest suffix later native).map Completion.event)
      apply List.Pairwise.cons _ (ih suffix later)
      intro event member
      obtain ⟨index, _inside, rfl⟩ :=
        (commitAttemptCompletions_event_mem whole mode rest suffix later native event).mp member
      change (embedding.event zero).val < (embedding.event (Fin.succ index)).val
      exact embedding.strictMono (by change 0 < index.val + 1; omega)

/-- Every canonical record retains exactly the native accepted typed meaning. -/
theorem commitAttemptCompletions_binding
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode)) :
    ∀ completion ∈ commitAttemptCompletions whole mode block suffix embedding native,
      ∃ owner payload, ∃ binding : outputLayout whole completion.event = .binding owner payload,
        cast (congrArg EventField.Action binding) completion.action =
          (native.accepted (.inr completion.event)).elim .failure
            (fun candidate => native.bindingResult candidate payload) := by
  induction block with
  | nil => intro completion member; cases member
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro completion member
      change completion ∈ _ :: _ at member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨owner, payload, ?_, ?_⟩
        · simpa only [CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero]
            using embedding.layout_eq ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
        · simp only [cast_cast, cast_eq]
      · exact ih suffix _ completion member

private theorem list_eq_of_map_eq_on_records
    {α β : Type} (f : α → β) (left right : List α) (same : left.map f = right.map f)
    (agree : ∀ a ∈ left, ∀ b ∈ right, f a = f b → a = b) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons => cases same
  | cons a tail ih =>
      cases right with
      | nil => cases same
      | cons b rest =>
          obtain ⟨heads, tails⟩ := List.cons.inj same
          have equal := agree a (List.mem_cons_self ..) b (List.mem_cons_self ..) heads
          subst b
          congr 1
          exact ih rest tails (fun x hx y hy =>
            agree x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))

/-- A sorted list of actual records with the same owned event set has the same
full dependent own recall, including the original binding values. -/
theorem EventGraph.Config.ownCompletions_eq_of_ordered_records
    {graph : EventGraph Player L} (config : graph.Config) (who : Player)
    (records : List graph.Completion)
    (ordered : (graph.ownEventIds who config.history).Pairwise
      (fun left right => left.val < right.val))
    (recordOrder : (graph.ownEventIds who records).Pairwise
      (fun left right => left.val < right.val))
    (actual : ∀ completion ∈ graph.ownCompletions who records, completion ∈ config.history)
    (events : ∀ event, event ∈ graph.ownEventIds who config.history ↔
      event ∈ graph.ownEventIds who records) :
    graph.ownCompletions who config.history = graph.ownCompletions who records := by
  have identities := ordered.eq_of_mem_iff recordOrder events
  apply list_eq_of_map_eq_on_records Completion.event _ _ identities
  intro left member right recorded same
  have leftIn := (List.mem_filter.mp member).1
  have rightIn := actual right recorded
  have injective := List.inj_on_of_nodup_map config.history_nodup
  exact injective leftIn rightIn same

end Vegas
