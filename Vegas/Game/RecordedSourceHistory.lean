/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitAttemptRecall
import Vegas.EventGraph.SequentialLaw

/-! # Source action words certified by actual ranked completion records -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

/-- The exact source action word contributed by an actual completed interval. -/
def RecordedSourceHistory
    (config : ((toEventGraph whole).withMode mode).Config) (offset count : Nat)
    (before after : SourceProgram.History Player L) (excluded : Finset Player) : Prop :=
  ∃ records : List ((toEventGraph whole).withMode mode).Completion,
    (records.map Completion.event).Pairwise (fun left right => left.val < right.val) ∧
    (∀ completion ∈ records, completion ∈ config.history) ∧
    (∀ event, event ∈ records.map Completion.event ↔
      offset ≤ event.val ∧ event.val < offset + count) ∧
    ∀ who, who ∉ excluded → after who = before who ++ decodeHistory whole
      (records.map ((toEventGraph whole).fromModeCompletion mode)) who

private theorem history_append (first second : List (toEventGraph whole).Completion)
    (who : Player) : decodeHistory whole (first ++ second) who =
      decodeHistory whole first who ++ decodeHistory whole second who := by
  simp only [decodeHistory, ownCompletions, List.filter_append, decodeCompletions_append]

private theorem mode_history (who : Player)
    (past : List ((toEventGraph whole).withMode mode).Completion) :
    decodeHistory whole (past.map ((toEventGraph whole).fromModeCompletion mode)) who =
      decodeCompletions whole
        ((((toEventGraph whole).withMode mode).ownCompletions who past).map
          ((toEventGraph whole).fromModeCompletion mode)) := by
  simp only [decodeHistory, ownCompletions, List.filter_map]
  rfl

private theorem singleton_history
    (completion : ((toEventGraph whole).withMode mode).Completion)
    (action : OwnAction Player L)
    (decoded : decodeEventAction whole completion.event completion.action = some action)
    (who : Player) :
    decodeHistory whole [((toEventGraph whole).fromModeCompletion mode completion)] who =
      if who = sourceActionOwner action then [action] else [] := by
  have first := decodeHistory_append_completion whole [] completion.event completion.action
  rw [decoded] at first
  simp only [List.nil_append] at first
  change decodeHistory whole [⟨completion.event, completion.action⟩] who = _
  rw [first]
  simp only [decodeHistory, ownCompletions, List.filter_nil, decodeCompletions,
    List.filterMap_nil, Function.update_apply, List.nil_append]

namespace RecordedSourceHistory

/-- An empty interval appends no source action. -/
theorem empty (config : ((toEventGraph whole).withMode mode).Config) (offset : Nat)
    (history : SourceProgram.History Player L) (excluded : Finset Player) :
    RecordedSourceHistory whole mode config offset 0 history history excluded := by
  refine ⟨[], .nil, (fun _ impossible => by cases impossible), ?_, ?_⟩
  · intro event
    simp only [List.map_nil, List.not_mem_nil, Nat.add_zero, false_iff, not_and]
    omega
  · intro who active
    simp only [List.map_nil, decodeHistory, ownCompletions, List.filter_nil,
      decodeCompletions, List.filterMap_nil, List.append_nil]

/-- A recorded chance step changes no owned source action. -/
theorem sample (config : ((toEventGraph whole).withMode mode).Config) (offset : Nat)
    (history : SourceProgram.History Player L)
    (completion : ((toEventGraph whole).withMode mode).Completion)
    (recorded : completion ∈ config.history) (rank : completion.event.val = offset)
    (decoded : decodeEventAction whole completion.event completion.action = none)
    (excluded : Finset Player) :
    RecordedSourceHistory whole mode config offset 1 history history excluded := by
  refine ⟨[completion], by simp, (fun _ member => by
      obtain rfl := List.mem_singleton.mp member
      exact recorded), ?_, ?_⟩
  · intro event
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    constructor
    · rintro rfl; omega
    · intro bounds
      exact Fin.ext (by omega)
  · intro who active
    have first := decodeHistory_append_completion whole [] completion.event completion.action
    rw [decoded] at first
    simp only [List.nil_append] at first
    change history who = history who ++ decodeHistory whole [⟨completion.event, completion.action⟩]
      who
    rw [first]
    simp only [decodeHistory, ownCompletions, List.filter_nil, decodeCompletions,
      List.filterMap_nil, List.append_nil]

/-- Prepending the actual recorded source action retains its exact bit/value. -/
theorem cons
    (config : ((toEventGraph whole).withMode mode).Config) (offset count : Nat)
    (before middle after : SourceProgram.History Player L) (excluded : Finset Player)
    (completion : ((toEventGraph whole).withMode mode).Completion)
    (recorded : completion ∈ config.history) (rank : completion.event.val = offset)
    (action : OwnAction Player L)
    (decoded : decodeEventAction whole completion.event completion.action = some action)
    (appended : ∀ who, who ∉ excluded → middle who =
      (Function.update before (sourceActionOwner action)
        (before (sourceActionOwner action) ++ [action])) who)
    (later : RecordedSourceHistory whole mode config (offset + 1) count middle after excluded) :
    RecordedSourceHistory whole mode config offset (count + 1) before after excluded := by
  obtain ⟨records, sorted, actual, events, history⟩ := later
  refine ⟨completion :: records, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.pairwise_cons]
    refine ⟨?_, sorted⟩
    intro event member
    have lower := ((events event).mp member).1
    omega
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact recorded
    · exact actual other member
  · intro event
    simp only [List.map_cons, List.mem_cons, events]
    constructor
    · rintro (rfl | bounds) <;> omega
    · intro bounds
      by_cases first : event.val = offset
      · exact Or.inl (Fin.ext (by omega))
      · right; omega
  · intro who active
    rw [history who active, appended who active, List.map_cons, show
      ((toEventGraph whole).fromModeCompletion mode completion) ::
        records.map ((toEventGraph whole).fromModeCompletion mode) =
      [((toEventGraph whole).fromModeCompletion mode completion)] ++
        records.map ((toEventGraph whole).fromModeCompletion mode) from rfl,
      history_append, singleton_history whole mode completion action decoded]
    by_cases same : who = sourceActionOwner action
    · subst who
      simp only [Function.update_self, ↓reduceIte, List.append_assoc]
    · simp only [Function.update_of_ne same, same, ↓reduceIte, List.nil_append]

private theorem own_ids_mem {graph : EventGraph Player L} (who : Player)
    (past : List graph.Completion) (event : graph.EventId) :
    event ∈ graph.ownEventIds who past ↔
      event ∈ past.map Completion.event ∧ graph.actor? event = some who := by
  unfold ownEventIds ownCompletions
  constructor
  · intro member
    obtain ⟨completion, present, same⟩ := List.mem_map.mp member
    subst event
    exact ⟨List.mem_map.mpr ⟨completion, (List.mem_filter.mp present).1, rfl⟩,
      of_decide_eq_true (List.mem_filter.mp present).2⟩
  · rintro ⟨member, owned⟩
    obtain ⟨completion, present, same⟩ := List.mem_map.mp member
    subst event
    exact List.mem_map.mpr ⟨completion, List.mem_filter.mpr ⟨present, by
      simpa only [decide_eq_true_eq] using owned⟩, rfl⟩

/-- Actual source-ranked records identify the full physical own word, including
all original dependent actions, without equating foreign completion orders. -/
theorem native_history_extension
    (entry current : ((toEventGraph whole).withMode mode).Config)
    (offset count : Nat) (before after : SourceProgram.History Player L)
    (excluded : Finset Player)
    (word : RecordedSourceHistory whole mode current offset count before after excluded)
    {inputs} (reachable : current.Reachable inputs)
    (retained : entry.history.IsPrefix current.history)
    (saved : entry.cut.IsPrefix offset) (finished : current.cut.IsPrefix (offset + count))
    (who : Player) (active : who ∉ excluded) :
    after who = before who ++
      (decodeHistory whole (current.history.map
        ((toEventGraph whole).fromModeCompletion mode)) who).drop
          (decodeHistory whole (entry.history.map
            ((toEventGraph whole).fromModeCompletion mode)) who).length := by
  obtain ⟨records, sorted, actual, events, history⟩ := word
  have relaxed := (toEventGraph whole).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered whole) mode
  have ordered := relaxed.ownEventIds_pairwise reachable who
  have ownRecall := current.ownCompletions_eq_of_ordered_records who (entry.history ++ records)
    ordered ?_ ?_ ?_
  · rw [history who active]
    have decoded := congrArg (fun past => decodeCompletions whole
      (past.map ((toEventGraph whole).fromModeCompletion mode))) ownRecall
    rw [← mode_history whole mode who _, ← mode_history whole mode who _, List.map_append,
      history_append] at decoded
    rw [decoded]
    simp only [List.drop_left]
  · simp only [ownEventIds, ownCompletions, List.filter_append, List.map_append,
      List.pairwise_append]
    refine ⟨ordered.sublist ((retained.sublist.filter _).map _),
      sorted.sublist (List.filter_sublist.map _), ?_⟩
    intro earlier earlierMember later laterMember
    have previous := (own_ids_mem who entry.history earlier).mp earlierMember
    have old := (saved.2 earlier).mp ((entry.history_exact earlier).mp previous.1)
    have new := (own_ids_mem who records later).mp laterMember
    have lower := ((events later).mp new.1).1
    omega
  · intro completion member
    have member := (List.mem_filter.mp member).1
    rcases List.mem_append.mp member with old | new
    · exact retained.subset old
    · exact actual completion new
  · intro event
    rw [own_ids_mem, own_ids_mem, List.map_append, List.mem_append]
    constructor
    · rintro ⟨done, actor⟩
      have upper := (finished.2 event).mp ((current.history_exact event).mp done)
      by_cases old : event.val < offset
      · exact ⟨Or.inl ((entry.history_exact event).mpr ((saved.2 event).mpr old)), actor⟩
      · exact ⟨Or.inr ((events event).mpr (by omega)), actor⟩
    · rintro ⟨old | new, actor⟩
      · obtain ⟨completion, member, rfl⟩ := List.mem_map.mp old
        exact ⟨List.mem_map.mpr ⟨completion, retained.subset member, rfl⟩, actor⟩
      · obtain ⟨completion, member, rfl⟩ := List.mem_map.mp new
        exact ⟨List.mem_map.mpr ⟨completion, actual completion member, rfl⟩, actor⟩

/-- Exact saved own words identify the surviving full native source word. -/
theorem native_history
    (entry current : ((toEventGraph whole).withMode mode).Config)
    (offset count : Nat) (before after : SourceProgram.History Player L)
    (excluded : Finset Player)
    (word : RecordedSourceHistory whole mode current offset count before after excluded)
    {inputs} (reachable : current.Reachable inputs)
    (retained : entry.history.IsPrefix current.history)
    (saved : entry.cut.IsPrefix offset) (finished : current.cut.IsPrefix (offset + count))
    (aligned : ∀ who, who ∉ excluded → before who = decodeHistory whole
      (entry.history.map ((toEventGraph whole).fromModeCompletion mode)) who)
    (who : Player) (active : who ∉ excluded) :
    after who = decodeHistory whole
      (current.history.map ((toEventGraph whole).fromModeCompletion mode)) who := by
  rw [native_history_extension whole mode entry current offset count before after excluded word
    reachable retained saved finished who active, aligned who active]
  obtain ⟨later, complete⟩ := retained
  rw [← complete, List.map_append, history_append]
  simp only [List.drop_left]

end RecordedSourceHistory
end Vegas
