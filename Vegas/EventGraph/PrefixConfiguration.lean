module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PrefixRestriction
public import Vegas.EventGraph.DecisionTwin

@[expose] public section

/-! # Recovering a graph checkpoint from a later configuration -/

namespace Vegas.EventGraph.Config

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Retain the inputs and all completions below the given rank in their actual
chronological order. Predecessors have lower ranks, so the surviving cut is closed. -/
def rankPrefix (rank : Nat) (config : graph.Config) : graph.Config where
  inputs := config.inputs
  cut := {
    completed := config.cut.completed.filter fun event => event.val < rank
    predecessor_closed := by
      intro event completed other prior
      obtain ⟨member, smaller⟩ := Finset.mem_filter.mp completed
      exact Finset.mem_filter.mpr ⟨config.cut.predecessor_closed member prior,
        (graph.order.predecessor_lt prior).trans smaller⟩ }
  outputs := fun event => if event.val < rank then config.outputs event else none
  output_available := by
    intro event
    by_cases smaller : event.val < rank <;> simp [smaller, config.output_available]
  history := config.history.filter fun record => record.event.val < rank
  history_nodup := config.history_nodup.sublist ((List.filter_sublist).map _)
  history_exact := by
    intro event
    change event ∈ (config.history.filter _).map EventCompletion.event ↔
      event ∈ config.cut.completed.filter _
    rw [Finset.mem_filter, ← config.history_exact, List.mem_map, List.mem_map]
    constructor
    · rintro ⟨record, inside, rfl⟩
      obtain ⟨member, smaller⟩ := List.mem_filter.mp inside
      exact ⟨⟨record, member, rfl⟩, of_decide_eq_true smaller⟩
    · rintro ⟨⟨record, member, rfl⟩, smaller⟩
      exact ⟨record, List.mem_filter.mpr ⟨member, decide_eq_true smaller⟩, rfl⟩

variable [DecidableEq Player]

/-- Restricting any later reachable configuration to the rank of a prefix
recovers its exact graph state, including inputs, hidden outputs and history. -/
theorem rankPrefix_of_path {before after : graph.Config} {rank : Nat}
    (ordered : before.cut.IsPrefix rank) (path : Relation.ReflTransGen Step before after) :
    rankPrefix rank after = before := by
  apply ext_fields
  · change after.inputs = before.inputs
    exact Step.path_inputs_eq path
  · apply EventOrder.Cut.ext
    ext event
    change event ∈ after.cut.completed.filter _ ↔ event ∈ before.cut.completed
    rw [Finset.mem_filter, ordered.2]
    exact ⟨And.right, fun small => ⟨Step.path_completed_mono path ((ordered.2 _).mpr small),
      small⟩⟩
  · funext event
    exact ((restrictionOf_path ordered path).store (.inr event)).symm
  · obtain ⟨tail, history⟩ := Step.path_history_prefix path
    have disjoint := after.history_nodup
    rw [← history, List.map_append] at disjoint
    have earlier : (before.history.filter fun record => record.event.val < rank) =
        before.history := by
      apply List.filter_eq_self.mpr
      intro record member
      exact decide_eq_true ((ordered.2 _).mp ((before.history_exact _).mp
        (List.mem_map.mpr ⟨record, member, rfl⟩)))
    have later : (tail.filter fun record => record.event.val < rank) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro record member small
      exact disjoint.disjoint ((before.history_exact _).mpr ((ordered.2 _).mpr
        (of_decide_eq_true small))) (List.mem_map.mpr ⟨record, member, rfl⟩)
    change (after.history.filter _) = before.history
    rw [← history, List.filter_append, earlier, later, List.append_nil]

end Vegas.EventGraph.Config

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The rank readout of a complete canonical game has exactly the law of its
bounded runner stopped at that rank. -/
theorem runPolicies_rankPrefix (profile : graph.BehavioralProfile) (inputs : graph.Inputs)
    (rank : Nat) (bounded : rank ≤ graph.order.eventCount) :
    (graph.runPolicies graph.canonicalScheduler profile inputs).map (Config.rankPrefix rank) =
      graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) rank
        (Config.initial inputs) := by
  let plan := graph.policyPlan profile graph.canonicalScheduler
  change (graph.runPlan plan graph.order.eventCount _).map _ = _
  rw [show graph.order.eventCount = rank + (graph.order.eventCount - rank) by omega,
    graph.runPlan_add, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (graph.runPlan plan rank (Config.initial inputs))]
  apply bind_congr_on_support _
  intro before reached
  have ordered : before.cut.IsPrefix rank := by
    simpa only [Nat.zero_add] using runPlan_canonical_isPrefix profile rank 0
      (Config.initial inputs)
      (EventOrder.Cut.empty_isPrefix _) (by simpa only [Nat.zero_add] using bounded) before reached
  rw [map_congr_on_support _ (g := fun _ => before) (fun after member =>
    Config.rankPrefix_of_path ordered (runPlan_graph_steps plan _ before after member)),
    pmf_map_fun_const]

end Vegas.EventGraph
