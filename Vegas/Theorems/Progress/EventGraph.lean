import Vegas.EventGraph.Basic

/-!
# Event-Graph Progress

Facts about enabledness, frontiers, terminality, and rank-minimal progress that
hold for every `EventGraph`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- In any event graph, the frontier is exactly the set of enabled nodes. -/
theorem eventGraph_mem_frontier_iff_enabled
    {G : EventGraph P L} (cfg : G.Configuration) (node : G.Node) :
    node ∈ cfg.frontier ↔ cfg.Enabled node :=
  cfg.mem_frontier_iff node

/-- Frontier nodes belong to the graph's declared node set. -/
theorem eventGraph_frontier_node_mem_nodes
    {G : EventGraph P L} {cfg : G.Configuration} {node : G.Node}
    (hfrontier : node ∈ cfg.frontier) :
    node ∈ G.nodes :=
  cfg.mem_nodes_of_mem_frontier hfrontier

/-- Frontier nodes have not yet produced a result. -/
theorem eventGraph_frontier_node_not_done
    {G : EventGraph P L} {cfg : G.Configuration} {node : G.Node}
    (hfrontier : node ∈ cfg.frontier) :
    (cfg.result node).isNone :=
  cfg.not_done_of_mem_frontier hfrontier

/-- Every prerequisite of a frontier node is already done. -/
theorem eventGraph_frontier_prereq_done
    {G : EventGraph P L} {cfg : G.Configuration} {node prereq : G.Node}
    (hfrontier : node ∈ cfg.frontier)
    (hpre : prereq ∈ G.prereqs node) :
    prereq ∈ cfg.done :=
  cfg.prereq_done_of_mem_frontier hfrontier hpre

/-- Every prerequisite of a frontier node has a stored result. -/
theorem eventGraph_frontier_prereq_result_isSome
    {G : EventGraph P L} {cfg : G.Configuration} {node prereq : G.Node}
    (hfrontier : node ∈ cfg.frontier)
    (hpre : prereq ∈ G.prereqs node) :
    (cfg.result prereq).isSome :=
  cfg.result_some_of_prereq_of_mem_frontier hfrontier hpre

/-- Two current frontier nodes cannot stand in the prerequisite relation. -/
theorem eventGraph_frontier_nodes_not_prereq
    {G : EventGraph P L} {cfg : G.Configuration} {first second : G.Node}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier) :
    first ∉ G.prereqs second :=
  EventGraph.Configuration.not_prereq_of_mem_frontier hfirst hsecond

/-- A configuration with a frontier node is nonterminal. -/
theorem eventGraph_not_terminal_of_mem_frontier
    {G : EventGraph P L} {cfg : G.Configuration} {node : G.Node}
    (hfrontier : node ∈ cfg.frontier) :
    ¬ cfg.terminal :=
  cfg.not_terminal_of_mem_frontier hfrontier

/-- A nonterminal event-graph configuration has a nonempty frontier. -/
theorem eventGraph_frontier_nonempty_of_not_terminal
    {G : EventGraph P L} {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    cfg.frontier.Nonempty :=
  cfg.frontier_nonempty_of_not_terminal hterminal

/-- A rank-minimal unfinished node is enabled. -/
theorem eventGraph_rank_minimal_unfinished_enabled
    {G : EventGraph P L} {cfg : G.Configuration} {node : G.Node}
    (hnode : node ∈ G.nodes)
    (hunfin : (cfg.result node).isNone)
    (hmin :
      ∀ other, other ∈ G.nodes → (cfg.result other).isNone →
        G.rank node ≤ G.rank other) :
    cfg.Enabled node :=
  cfg.enabled_of_rank_minimal_unfinished hnode hunfin hmin

/-- In a nonterminal configuration, some rank-minimal unfinished node is on the
frontier. -/
theorem eventGraph_exists_rank_minimal_frontier_of_not_terminal
    {G : EventGraph P L} {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    ∃ node, node ∈ cfg.frontier ∧
      ∀ other, other ∈ G.nodes → (cfg.result other).isNone →
        G.rank node ≤ G.rank other := by
  rcases cfg.exists_rank_minimal_enabled_of_not_terminal hterminal with
    ⟨node, henabled, hmin⟩
  exact ⟨node, (cfg.mem_frontier_iff node).mpr henabled, hmin⟩

/-- Terminality means every graph node is done. -/
theorem eventGraph_terminal_iff_all_nodes_done
    {G : EventGraph P L} (cfg : G.Configuration) :
    cfg.terminal ↔ G.nodes ⊆ cfg.done :=
  Iff.rfl

end Vegas
