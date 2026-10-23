/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Information

/-! # Observation congruence for graph completions -/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Completion metadata determines the current cut, independently of all
stored values and supplied private actions. -/
theorem cut_eq_of_completionOrder_eq (left right : graph.Config)
    (order : left.history.map Completion.event = right.history.map Completion.event) :
    left.cut = right.cut := by
  apply EventOrder.Cut.ext
  apply Finset.ext
  intro event
  rw [← left.history_exact, ← right.history_exact, order]

omit [DecidableEq Player] in
/-- Extending chronological history preserves every completed event. -/
theorem completed_subset_of_history_prefix (before after : graph.Config)
    (histories : before.history.IsPrefix after.history) :
    before.cut.completed ⊆ after.cut.completed := by
  intro event completed
  rw [← after.history_exact]
  exact (histories.map Completion.event).subset ((before.history_exact event).mpr completed)

/-- Equal player observations identify all fields visible to that player. -/
theorem store_eq_of_playerObserve_eq (who : Player) (left right : graph.Config)
    (observations : graph.playerObserve who left = graph.playerObserve who right)
    (field : graph.Field) (visible : graph.fieldVisibleTo who field) :
    left.store field = right.store field := by
  have stores := congrArg (fun view : graph.PlayerObservation who => view.store) observations
  have atField := congrFun stores field
  simpa only [playerObserve, playerStore_of_visible, visible] using atField

/-- The public observation is a projection of every player's observation. -/
theorem publicObserve_eq_of_playerObserve_eq (who : Player) (left right : graph.Config)
    (observations : graph.playerObserve who left = graph.playerObserve who right) :
    graph.publicObserve left = graph.publicObserve right := by
  apply PublicObservation.ext graph
  · exact congrArg PlayerObservation.completionOrder observations
  · apply graph.publicStore_congr
    intro field isPublic
    apply store_eq_of_playerObserve_eq who left right observations field
    change (graph.layout field).VisibleTo who
    cases kind : graph.layout field <;>
      simp_all [fieldPublic, EventField.IsPublic, EventField.VisibleTo]

/-- Completing the same event preserves equal observations provided its
visible value and its observer-owned action agree. Foreign private binding
values and foreign action choices remain unrelated. -/
theorem playerObserve_complete_congr (who : Player) (left right : graph.Config)
    (observations : graph.playerObserve who left = graph.playerObserve who right)
    (event : graph.EventId) (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftValue rightValue : (graph.outputLayout event).Value)
    (values : graph.fieldVisibleTo who (.inr event) → leftValue = rightValue)
    (actions : graph.actor? event = some who → leftAction = rightAction) :
    graph.playerObserve who (left.complete event leftReady leftAction leftValue) =
      graph.playerObserve who (right.complete event rightReady rightAction rightValue) := by
  have order := congrArg PlayerObservation.completionOrder observations
  have recall := congrArg PlayerObservation.ownActions observations
  apply PlayerObservation.ext graph
  · simpa only [playerObserve, Config.complete_history, List.map_append,
      List.map_cons, List.map_nil] using congrArg (fun prior => prior ++ [event]) order
  · apply graph.playerStore_congr
    intro field visible
    cases field with
    | inl input => exact store_eq_of_playerObserve_eq who left right observations _ visible
    | inr query =>
        by_cases same : query = event
        · subst query
          change (left.complete event leftReady leftAction leftValue).outputs event =
            (right.complete event rightReady rightAction rightValue).outputs event
          rw [Config.complete_output_same, Config.complete_output_same, values visible]
        · change (left.complete event leftReady leftAction leftValue).outputs query =
            (right.complete event rightReady rightAction rightValue).outputs query
          rw [Config.complete_output_of_ne _ _ _ _ _ _ same,
            Config.complete_output_of_ne _ _ _ _ _ _ same]
          exact store_eq_of_playerObserve_eq who left right observations _ visible
  · change graph.ownCompletions who (left.history ++ [⟨event, leftAction⟩]) =
      graph.ownCompletions who (right.history ++ [⟨event, rightAction⟩])
    change graph.ownCompletions who left.history = graph.ownCompletions who right.history at recall
    by_cases owned : graph.actor? event = some who
    · simp only [ownCompletions, List.filter_append] at *
      rw [recall, actions owned]
    · simp only [ownCompletions, List.filter_append, List.filter_cons, owned,
        decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
      exact recall

end Vegas.EventGraph
