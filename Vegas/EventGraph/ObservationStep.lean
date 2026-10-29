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
  · exact congrArg PlayerObservation.defaults observations

/-- Equal visible values, own choices and new public default entries preserve
equal observations. Foreign private binding values and action choices need
agree only through their public default effect. -/
theorem playerObserve_complete_congr (who : Player) (left right : graph.Config)
    (observations : graph.playerObserve who left = graph.playerObserve who right)
    (event : graph.EventId) (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftValue rightValue : (graph.outputLayout event).Value)
    (values : graph.fieldVisibleTo who (.inr event) → leftValue = rightValue)
    (actions : graph.actor? event = some who → leftAction = rightAction)
    (publicEffect :
      (Completion.fromDecision event
        (left.actualDecision event leftAction) leftValue).defaultEvent =
        (Completion.fromDecision event
          (right.actualDecision event rightAction) rightValue).defaultEvent) :
    graph.playerObserve who (left.complete event leftReady leftAction leftValue) =
      graph.playerObserve who (right.complete event rightReady rightAction rightValue) := by
  have order := congrArg PlayerObservation.completionOrder observations
  have recall := congrArg PlayerObservation.ownActions observations
  have defaults : left.defaults = right.defaults :=
    congrArg PlayerObservation.defaults observations
  have status : left.defaulted = right.defaulted :=
    congrArg DefaultHistory.defaulted defaults
  apply PlayerObservation.ext graph
  · simpa only [playerObserve, Config.complete_history, List.map_append,
      List.map_cons, List.map_nil, Completion.fromDecision] using
        congrArg (fun prior => prior ++ [event]) order
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
  · change graph.ownCompletions who left.history =
      graph.ownCompletions who right.history at recall
    by_cases owned : graph.actor? event = some who
    · have decision : left.actualDecision event leftAction =
          right.actualDecision event rightAction := by
        unfold Config.actualDecision
        rw [status, actions owned]
      have completion : Completion.fromDecision event
          (left.actualDecision event leftAction) leftValue =
            Completion.fromDecision event (right.actualDecision event rightAction) rightValue :=
        congrArg₂ (fun choice defaultEvent =>
          (⟨event, choice, defaultEvent⟩ : graph.Completion)) decision publicEffect
      change graph.ownCompletions who (left.history ++
          [Completion.fromDecision event (left.actualDecision event leftAction) leftValue]) =
        graph.ownCompletions who (right.history ++
          [Completion.fromDecision event (right.actualDecision event rightAction) rightValue])
      simp only [ownCompletions, List.filter_append] at recall ⊢
      rw [recall, completion]
    · exact (graph.ownCompletions_complete_of_not_actor who left event
        leftReady leftAction leftValue owned).trans
        (recall.trans (graph.ownCompletions_complete_of_not_actor who right event
          rightReady rightAction rightValue owned).symm)
  · change (left.complete event leftReady leftAction leftValue).defaults =
      (right.complete event rightReady rightAction rightValue).defaults
    rw [Config.complete_defaults, Config.complete_defaults]
    exact congrArg₂ DefaultHistory.record defaults publicEffect

end Vegas.EventGraph
