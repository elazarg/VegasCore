module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.SchedulerReplay
public import Vegas.EventGraph.DecisionTwin
public import Vegas.EventGraph.SequentialDistribution
public import Vegas.EventGraph.SequentialNormalization
public import Vegas.EventGraph.NormalizedRestriction

@[expose] public section

/-! # Terminal configurations in source rank

A terminal cut can be read in rank order without changing its typed values or
individual completion records. The result is a configuration of the existing
sequential specialization, and canonical sequential execution is unchanged.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The completions of a configuration listed in event rank, one per completed event. -/
def rankedHistory {graph : Vegas.EventGraph Player L} (config : graph.Config) :
    List graph.Completion :=
  (List.finRange graph.order.eventCount).filterMap (completionOf config)

omit [DecidableEq Player] in
theorem rankedHistory_events {graph : Vegas.EventGraph Player L} (config : graph.Config) :
    (rankedHistory config).map EventCompletion.event =
      (List.finRange graph.order.eventCount).filter fun event =>
        (completionOf config event).isSome := by
  unfold rankedHistory
  rw [List.map_filterMap]
  have tagged (event : graph.EventId) :
      (completionOf config event).map EventCompletion.event =
        if (completionOf config event).isSome then some event else none := by
    cases found : completionOf config event with
    | none => rfl
    | some completion =>
        simp [((completionOf_eq_some_iff config event completion).mp found).2]
  rw [List.filterMap_congr fun event _ => tagged event]
  induction (List.finRange graph.order.eventCount) with
  | nil => rfl
  | cons head tail ih =>
      cases present : (completionOf config head).isSome <;> simp [present, ih]

/-- Listing erased completions by rank erases only their private decisions. -/
theorem rankedHistory_erase {graph : EventGraph Player L} (config : graph.Config) :
    rankedHistory config.erase =
      (rankedHistory config).map (graph.eraseCompletion config.defaulted) := by
  unfold rankedHistory
  simp only [completionOf_erase]
  generalize List.finRange graph.order.eventCount = events
  induction events with
  | nil => rfl
  | cons head tail ih =>
      cases found : completionOf config head <;> simp [found, ih]


/-- A terminal configuration of the concurrent graph, as a configuration of the
compiled graph whose history lists completions in source order. -/
def rankedConfig
    (config : graph.Config) (terminal : config.cut.Terminal) :
    graph.sequentialize.Config where
  inputs := config.inputs
  cut := { completed := Finset.univ, predecessor_closed := fun _ _ _ => Finset.mem_univ _ }
  outputs := config.outputs
  output_available event := by
    rw [config.output_available, terminal]
  history := rankedHistory (graph := graph) config
  history_nodup := by
    have events : ((rankedHistory (graph := graph) config).map
        EventCompletion.event).Nodup := by
      rw [rankedHistory_events]
      exact (List.nodup_finRange _).filter _
    exact events
  history_exact event := by
    have events : event ∈ (rankedHistory (graph := graph) config).map
        EventCompletion.event := by
      rw [rankedHistory_events, List.mem_filter, ← mem_completed_iff_completionOf, terminal]
      simp
    exact ⟨fun _ => Finset.mem_univ _, fun _ => events⟩

omit [DecidableEq Player] in
theorem rankedConfig_terminal
    (config : graph.Config) (terminal : config.cut.Terminal) :
    (rankedConfig config terminal).cut.Terminal := rfl

omit [DecidableEq Player] in
/-- Recasting in source order keeps every completion record. -/
theorem completionOf_rankedConfig
    (config : graph.Config) (terminal : config.cut.Terminal) :
    completionOf (rankedConfig config terminal) = completionOf config := by
  funext event
  exact find?_filterMap_tagged (completionOf config) (completionOf_tagged config) event

/-- Recasting in source order keeps the defaulted players. -/
theorem defaulted_rankedConfig
    (config : graph.Config) (terminal : config.cut.Terminal) :
    (rankedConfig config terminal).defaulted = config.defaulted := by
  ext who
  rw [mem_defaulted_iff_completionOf, mem_defaulted_iff_completionOf,
    completionOf_rankedConfig]
  exact Iff.rfl

omit [DecidableEq Player] in
private theorem config_eq_of_data_eq {graph : Vegas.EventGraph Player L}
    {left right : graph.Config} (inputs : left.inputs = right.inputs)
    (cut : left.cut = right.cut) (outputs : left.outputs = right.outputs)
    (history : left.history = right.history) : left = right := by
  cases left
  cases right
  simp_all

omit [DecidableEq Player] in
/-- Rank reconstruction depends only on the store and individual completion records. -/
theorem rankedConfig_congr {left right : graph.Config} (same : runKey left = runKey right)
    (leftTerminal : left.cut.Terminal) (rightTerminal : right.cut.Terminal) :
    rankedConfig left leftTerminal = rankedConfig right rightTerminal := by
  have store : left.store = right.store := congrArg (fun key => key.2.1) same
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  apply config_eq_of_data_eq
  · funext input
    exact Option.some.inj (congrFun store (.inl input))
  · rfl
  · funext event
    exact congrFun store (.inr event)
  · change (List.finRange _).filterMap (completionOf left) =
      (List.finRange _).filterMap (completionOf right)
    rw [records]

omit [DecidableEq Player] in
private theorem map_val_finRange (count : Nat) :
    (List.finRange count).map Fin.val = List.range count := by
  apply List.ext_getElem <;> simp

/-- A terminal sequential execution is unchanged by rank reconstruction. -/
theorem rankedConfig_fromSequentialConfig
    {inputs : graph.sequentialize.Inputs} {config : graph.sequentialize.Config}
    (reach : Config.Reachable inputs config)
    (terminal : (graph.fromSequentialConfig config).cut.Terminal) :
    rankedConfig (graph.fromSequentialConfig config) terminal =
      config := by
  have complete : config.cut.Terminal := terminal
  have lengthEq : config.history.length = graph.sequentialize.order.eventCount := by
    have exact : config.cut.completed = (config.history.map EventCompletion.event).toFinset := by
      ext event
      rw [List.mem_toFinset, config.history_exact]
    have card := congrArg Finset.card exact
    rw [complete, Finset.card_univ, Fintype.card_fin,
      List.toFinset_card_of_nodup config.history_nodup, List.length_map] at card
    exact card.symm
  have events : config.history.map EventCompletion.event =
      List.finRange graph.sequentialize.order.eventCount := by
    apply List.map_injective_iff.mpr Fin.val_injective
    rw [List.map_map, map_val_finRange]
    have values := history_map_val_of_reachable (fun prior event earlier =>
      (EventOrder.sequential.mem_predecessors prior event).mpr earlier) reach
    rw [lengthEq] at values
    exact values
  have records : ∀ completion ∈ config.history,
      completionOf config completion.event = some completion := fun completion member =>
    (completionOf_eq_some_iff config completion.event completion).mpr ⟨member, rfl⟩
  apply config_eq_of_data_eq
  · rfl
  · ext event
    change event ∈ Finset.univ ↔ event ∈ config.cut.completed
    rw [complete]
  · rfl
  · change (List.finRange _).filterMap (completionOf config) = config.history
    rw [← events, List.filterMap_map]
    calc _ = config.history.filterMap some :=
          List.filterMap_congr fun completion member => records completion member
      _ = config.history := List.filterMap_some

end Vegas.EventGraph
