/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitAttemptRecall
import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Pending.PhaseFailureCoverage

/-! # Completed binding phases retain their exact source-ranked own actions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : ExecutionMode)

private theorem ownEventIds_mem {graph : EventGraph Player L} (who : Player)
    (history : List graph.Completion) (event : graph.EventId) :
    event ∈ graph.ownEventIds who history ↔
      event ∈ history.map Completion.event ∧ graph.actor? event = some who := by
  constructor
  · rintro member
    obtain ⟨completion, owned, rfl⟩ := List.mem_map.mp member
    obtain ⟨recorded, acting⟩ := List.mem_filter.mp owned
    exact ⟨List.mem_map.mpr ⟨completion, recorded, rfl⟩, of_decide_eq_true acting⟩
  · rintro ⟨recorded, acting⟩
    obtain ⟨completion, member, rfl⟩ := List.mem_map.mp recorded
    exact List.mem_map.mpr ⟨completion, List.mem_filter.mpr ⟨member, by
      simpa only [decide_eq_true_eq] using acting⟩, rfl⟩

/-- Native binding readback certifies every reconstructed dependent record,
including an accepted handle whose immutable typed meaning is failure. -/
theorem commitAttemptCompletions_recorded
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (valid : native.BindingInvariant) {inputs}
    (reachable : native.config.Reachable inputs)
    (who : Player)
    (completed : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      ((toEventGraph whole).withMode mode).actor? (embedding.event index) = some who →
        embedding.event index ∈ native.config.cut.completed) :
    ∀ completion ∈ (commitAttemptCompletions whole mode block suffix embedding native).map
        ((toEventGraph whole).toModeCompletion mode),
      ((toEventGraph whole).withMode mode).actor? completion.event = some who →
        completion ∈ native.config.history := by
  intro completion member acting
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, inside, named⟩ :=
    (commitAttemptCompletions_event_mem whole mode block suffix embedding native source.event).mp
      (List.mem_map.mpr ⟨source, sourceMember, rfl⟩)
  have done := completed index inside (by simpa only [named, toModeCompletion] using acting)
  rw [named] at done
  obtain ⟨owner, payload, binding, meaning⟩ :=
    commitAttemptCompletions_binding whole mode block suffix embedding native source sourceMember
  obtain ⟨action, recorded, actual⟩ :=
    valid.completed_binding_action reachable source.event owner payload binding done
  have equal : action = source.action := by
    have same := actual.trans meaning.symm
    have uncast := congrArg (cast (congrArg EventField.Action binding.symm)) same
    simpa only [cast_cast, cast_eq] using uncast
  cases equal
  exact recorded

/-- Chronological per-owner recall equals the saved word followed by the
source-ranked immutable binding records of this completed interval. -/
theorem commitAttemptCompletions_ownRecall
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (offset : Nat)
    (rank : ∀ index, (embedding.event index).val = offset + index.val)
    (entry native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (valid : native.BindingInvariant) {inputs}
    (reachable : native.config.Reachable inputs)
    (retained : entry.config.history.IsPrefix native.config.history)
    (saved : entry.config.cut.IsPrefix offset) (who : Player)
    (completedOwn : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      ((toEventGraph whole).withMode mode).actor? (embedding.event index) = some who →
        embedding.event index ∈ native.config.cut.completed)
    (boundedOwn : ∀ event ∈ native.config.cut.completed,
      ((toEventGraph whole).withMode mode).actor? event = some who →
        event.val < offset + block.length) :
    ((toEventGraph whole).withMode mode).ownCompletions who native.config.history =
      ((toEventGraph whole).withMode mode).ownCompletions who
        (entry.config.history ++
          (commitAttemptCompletions whole mode block suffix embedding native).map
            ((toEventGraph whole).toModeCompletion mode)) := by
  let graph := (toEventGraph whole).withMode mode
  let records := (commitAttemptCompletions whole mode block suffix embedding native).map
    ((toEventGraph whole).toModeCompletion mode)
  have actual := commitAttemptCompletions_recorded whole mode block suffix embedding native valid
    reachable who completedOwn
  have rawOrder : (records.map Completion.event).Pairwise
      (fun left right => left.val < right.val) := by
    simpa only [records, List.pairwise_map, toModeCompletion] using
      commitAttemptCompletions_pairwise whole mode block suffix embedding native
  have relaxed := (toEventGraph whole).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered whole) mode
  have ordered := relaxed.ownEventIds_pairwise reachable who
  apply native.config.ownCompletions_eq_of_ordered_records who
    (entry.config.history ++ records) ordered
  · simp only [ownEventIds, ownCompletions, List.filter_append, List.map_append,
      List.pairwise_append]
    refine ⟨ordered.sublist ((retained.sublist.filter _).map _),
      rawOrder.sublist (List.filter_sublist.map _), ?_⟩
    intro earlier earlierMember later laterMember
    have previous := (ownEventIds_mem who entry.config.history earlier).mp earlierMember
    have before := (saved.2 earlier).mp ((entry.config.history_exact earlier).mp previous.1)
    have next := (ownEventIds_mem who records later).mp laterMember
    have asSource : later ∈
        (commitAttemptCompletions whole mode block suffix embedding native).map Completion.event :=
      by simpa only [records, List.map_map, toModeCompletion, Function.comp_def] using next.1
    obtain ⟨index, _inside, named⟩ :=
      (commitAttemptCompletions_event_mem whole mode block suffix embedding native later).mp
        asSource
    rw [← named, rank]
    omega
  · intro completion member
    obtain ⟨recorded, acting⟩ := List.mem_filter.mp member
    rcases List.mem_append.mp recorded with old | new
    · exact retained.subset old
    · exact actual completion new (of_decide_eq_true acting)
  · intro event
    rw [ownEventIds_mem, ownEventIds_mem, List.map_append, List.mem_append]
    constructor
    · rintro ⟨present, actor⟩
      have below := boundedOwn event ((native.config.history_exact event).mp present) actor
      by_cases before : event.val < offset
      · exact ⟨Or.inl ((entry.config.history_exact event).mpr ((saved.2 event).mpr before)), actor⟩
      · have count := block.eventCount_prepend suffix
        let index : Fin (eventCount (block.prepend suffix)) := ⟨event.val - offset, by omega⟩
        have inside : index.val < block.length := by dsimp only [index]; omega
        have named : embedding.event index = event := by
          apply Fin.ext
          rw [rank]
          dsimp only [index]
          omega
        have member := (commitAttemptCompletions_event_mem whole mode block suffix embedding
          native event).mpr ⟨index, inside, named⟩
        refine ⟨Or.inr ?_, actor⟩
        simpa only [records, List.map_map, toModeCompletion, Function.comp_def] using member
    · rintro ⟨old | new, actor⟩
      · obtain ⟨completion, member, named⟩ := List.mem_map.mp old
        exact ⟨List.mem_map.mpr ⟨completion, retained.subset member, named⟩, actor⟩
      · obtain ⟨completion, member, named⟩ := List.mem_map.mp new
        have acting : graph.actor? completion.event = some who := by rwa [named]
        exact ⟨List.mem_map.mpr ⟨completion, actual completion member acting, named⟩, actor⟩

private theorem decodeHistory_fromMode (who : Player)
    (past : List ((toEventGraph whole).withMode mode).Completion) :
    decodeHistory whole (past.map ((toEventGraph whole).fromModeCompletion mode)) who =
      decodeCompletions whole
        ((((toEventGraph whole).withMode mode).ownCompletions who past).map
          ((toEventGraph whole).fromModeCompletion mode)) := by
  simp only [decodeHistory, ownCompletions, List.filter_map]
  rfl

/-- At a completed clear physical binding interval, the intrinsic accepted
attempt decoder has exactly the whole runtime's effective original own history.
Only the previously aligned saved history is supplied; all new actions and their
chronological order are derived from native reachability and binding readback. -/
theorem decodeCommitAttempt_history_of_clear_phase
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (offset : Nat)
    (rank : ∀ index, (embedding.event index).val = offset + index.val)
    (entryNative : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (current : RecoveryState ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ)
    (valid : current.native.BindingInvariant) {inputs}
    (reachable : current.native.config.Reachable inputs)
    (coverage : current.FailureCoverage) (clear : current.excluded = ∅)
    (retained : entryNative.config.history.IsPrefix current.native.config.history)
    (saved : entryNative.config.cut.IsPrefix offset)
    (finished : current.native.config.cut.IsPrefix (offset + block.length))
    (history : entry.history = decodeHistory whole (entryNative.config.history.map
      ((toEventGraph whole).fromModeCompletion mode)))
    (actions : ∀ index action, decodeEventAction whole (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action)) :
    (decodeCommitAttempt whole mode block suffix embedding current.native entry ∅).1.history =
      decodeHistory whole (current.native.config.history.map
        ((toEventGraph whole).fromModeCompletion mode)) := by
  have accepted (index : Fin (eventCount (block.prepend suffix)))
      (inside : index.val < block.length) :
      current.native.accepted (.inr (embedding.event index)) ≠ none := by
    obtain ⟨owner, payload, _member, binding⟩ := block.binding_before_length suffix index inside
    have kind := (embedding.layout_eq index).trans binding
    have actor : ((toEventGraph whole).withMode mode).actor? (embedding.event index) =
        some owner := by
      let code : EventCode ((toEventGraph whole).withMode mode).layout (.binding owner payload) :=
        cast (congrArg (EventCode ((toEventGraph whole).withMode mode).layout) kind)
          (((toEventGraph whole).withMode mode).nodes (embedding.event index))
      have codeActor : EventCode.actor code = some owner := by cases code; rfl
      exact (EventCode.actor_cast kind _).symm.trans codeActor
    intro missing
    have done := (finished.2 (embedding.event index)).mpr (by rw [rank]; omega)
    have failed : current.native.PublicFailure (embedding.event index) := Or.inl
      ((current.native.publicView_missedBinding _ owner payload kind).mpr ⟨done, missing⟩)
    have excluded := coverage.covered _ owner actor failed
    rw [clear] at excluded
    exact Finset.notMem_empty _ excluded
  have word := decodeCommitAttempt_history_of_accepted whole mode block suffix embedding
    current.native entry accepted actions
  funext who
  rw [word, history]
  have recall := commitAttemptCompletions_ownRecall whole mode block suffix embedding offset rank
    entryNative current.native valid reachable retained saved who
      (fun index inside _acting => (finished.2 _).mpr (by rw [rank]; omega))
      (fun event done _acting => (finished.2 event).mp done)
  have decoded := congrArg (fun past => decodeCompletions whole
    (past.map ((toEventGraph whole).fromModeCompletion mode))) recall
  rw [← decodeHistory_fromMode whole mode who _, ← decodeHistory_fromMode whole mode who _]
    at decoded
  have projected : ((commitAttemptCompletions whole mode block suffix embedding current.native).map
      ((toEventGraph whole).toModeCompletion mode)).map
        ((toEventGraph whole).fromModeCompletion mode) =
      commitAttemptCompletions whole mode block suffix embedding current.native := by
    rw [List.map_map]
    apply List.map_id''
    intro completion
    exact fromModeCompletion_toModeCompletion (toEventGraph whole) mode completion
  rw [List.map_append, projected] at decoded
  have append (first second : List (toEventGraph whole).Completion) :
      decodeHistory whole (first ++ second) who =
        decodeHistory whole first who ++ decodeHistory whole second who := by
    simp only [decodeHistory, ownCompletions, List.filter_append, decodeCompletions_append]
  rw [append] at decoded
  exact decoded.symm

end Vegas
