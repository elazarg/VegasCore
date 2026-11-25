module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PrefixRestriction

@[expose] public section

/-! # Recovering primary graph observations

A later graph observation retains the actual chronological view of a completed
rank prefix along any supported execution path.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Recover a rank prefix's view by restricting the visible store and retaining
the actual chronological completion order and default history. -/
def recoverPrefixObservation (rank : Nat) {who : Player}
    (observation : graph.PlayerObservation who) : graph.PlayerObservation who where
  completionOrder := observation.completionOrder.take rank
  store := fun field =>
    if FieldWithin (fun event => event.val < rank) field then observation.store field else none
  ownActions := observation.ownActions.filter fun record => record.event.val < rank
  defaults := ⟨(observation.defaults.events.reverse.take rank).reverse⟩

/-- The actual view at a numeric prefix is recovered from any later view along
a supported path. Private default markers are retained. -/
theorem recoverPrefixObservation_playerObserve (who : Player) {rank : Nat}
    {before after : graph.Config} (ordered : before.cut.IsPrefix rank)
    (path : Relation.ReflTransGen Config.Step before after) :
    recoverPrefixObservation rank (graph.playerObserve who after) =
      graph.playerObserve who before := by
  obtain ⟨tail, history⟩ := Config.Step.path_history_prefix path
  have length := before.history_length_of_isPrefix ordered
  apply EventPlayerObservation.ext
  · change (after.history.map EventCompletion.event).take rank = _
    rw [← history, List.map_append, ← length, ← List.length_map (f := EventCompletion.event),
      List.take_left]
    rfl
  · funext field
    change (if FieldWithin (fun event => event.val < rank) field then
      graph.playerStore who after.store field else none) = graph.playerStore who before.store field
    have stored := (Config.restrictionOf_path ordered path).store field
    by_cases visible : graph.fieldVisibleTo who field
    · simpa only [graph.playerStore_of_visible who _ field visible] using stored.symm
    · simp only [graph.playerStore_of_hidden who _ field visible, ite_self]
  · change ((graph.ownCompletions who after.history).filter fun record =>
      record.event.val < rank) = graph.ownCompletions who before.history
    have disjoint : List.Disjoint (before.history.map EventCompletion.event)
        (tail.map EventCompletion.event) := by
      have nodup := after.history_nodup
      rw [← history, List.map_append] at nodup
      exact nodup.disjoint
    have earlier (record : graph.Completion) (member : record ∈ before.history) :
        record.event.val < rank :=
      (ordered.2 record.event).mp ((before.history_exact record.event).mp
        (List.mem_map.mpr ⟨record, member, rfl⟩))
    have later (record : graph.Completion) (member : record ∈ tail) :
        ¬ record.event.val < rank := by
      intro prior
      exact disjoint ((before.history_exact record.event).mpr ((ordered.2 record.event).mpr prior))
        (List.mem_map.mpr ⟨record, member, rfl⟩)
    have priorActions : ((graph.ownCompletions who before.history).filter fun record =>
        record.event.val < rank) = graph.ownCompletions who before.history := by
      apply List.filter_eq_self.mpr
      intro record member
      exact decide_eq_true (earlier record (List.mem_of_mem_filter member))
    have laterActions : ((graph.ownCompletions who tail).filter fun record =>
        record.event.val < rank) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro record member
      exact fun yes => later record (List.mem_of_mem_filter member) (of_decide_eq_true yes)
    rw [← history, show graph.ownCompletions who (before.history ++ tail) =
      graph.ownCompletions who before.history ++ graph.ownCompletions who tail from
        List.filter_append _ _, List.filter_append, priorActions, laterActions, List.append_nil]
  · change DefaultHistory.mk (after.defaults.events.reverse.take rank).reverse = before.defaults
    simp only [Config.defaults, EventCompletion.defaults, List.reverse_reverse, ← history,
      List.map_append, ← length, ← List.length_map (f := EventCompletion.defaultEvent),
      List.take_left]

/-- A later observation following the primary event recovers the actual
observation at that event's canonical prefix. -/
theorem recoverPrefixObservation_playerObserve_of_step_path (who : Player)
    {before middle after : graph.Config} (event : graph.EventId)
    (ordered : before.cut.IsPrefix event.val) (ready : before.cut.Ready event)
    (action : graph.Action event) (moved : middle ∈ (before.step event ready action).support)
    (path : Relation.ReflTransGen Config.Step middle after) :
    recoverPrefixObservation event.val (graph.playerObserve who after) =
      graph.playerObserve who before :=
  recoverPrefixObservation_playerObserve who ordered
    ((Relation.ReflTransGen.single ⟨event, ready, action, moved⟩).trans path)

end Vegas.EventGraph
