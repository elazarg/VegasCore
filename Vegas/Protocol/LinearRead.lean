import Vegas.Protocol.SyntaxGraph

/-!
# Syntax-linear reading of protocol graphs

This file gives a small formal version of the programmer-facing reading
principle: source syntax may be read as a straight-line protocol order without
getting stuck. The executable semantics remains graph/machine-native; the
linear read is a presentation of the same dependency graph.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The source-linear presentation of a checked program's protocol events. -/
def syntaxLinearRead (g : WFProgram P L) : List (ProgramNode g.prog) :=
  ProgramNode.enumerate g.prog

@[simp] theorem mem_syntaxLinearRead
    (g : WFProgram P L) (node : ProgramNode g.prog) :
    node ∈ syntaxLinearRead g :=
  ProgramNode.mem_enumerate node

/-- Source-linear order is topological for the compiled syntax graph:
every graph prerequisite has smaller source rank than the node that reads it.

This is the static reason that a straight-line reading is sufficient. -/
theorem syntaxLinearRead_prereq_rank_lt
    (g : WFProgram P L)
    {node prereq : ProgramNode g.prog}
    (hpre : prereq ∈ (syntaxProtocolGraph g).prereqs node) :
    prereq.rank < node.rank :=
  (syntaxProtocolGraph g).prereq_rank_lt
    (by
      change node ∈ ProgramNode.finset g.prog
      exact ProgramNode.mem_finset g.prog node) hpre

/-- If a node is the first unfinished source node by source rank, then it is
on the executable graph frontier.

This is the local "linear read is sufficient" theorem: the reader can scan the
source-order nodes, stop at the first one not yet executed, and that node is a
legal next graph event whenever the graph has not terminated. -/
theorem syntaxLinearRead_rank_minimal_unfinished_mem_frontier
    (g : WFProgram P L)
    (cfg : (syntaxProtocolGraph g).Configuration)
    {node : ProgramNode g.prog}
    (hunfinished : (cfg.result node).isNone)
    (hmin :
      ∀ other : ProgramNode g.prog,
        other ∈ ProgramNode.finset g.prog →
          (cfg.result other).isNone →
            node.rank ≤ other.rank) :
    node ∈ cfg.frontier := by
  exact (ProtocolGraph.Configuration.mem_frontier_iff cfg node).mpr <|
    cfg.ready_of_rank_minimal_unfinished
    (by
      change node ∈ ProgramNode.finset g.prog
      exact ProgramNode.mem_finset g.prog node)
    hunfinished
    (by
      intro other hother hotherUnfinished
      exact hmin other (ProgramNode.mem_finset g.prog other)
        hotherUnfinished)

/-- Every nonterminal syntax graph has a frontier node that is earliest among
unfinished source nodes.

Thus the straight-line/source-rank presentation never gets stuck before the
graph-machine semantics does. -/
theorem syntaxLinearRead_sufficient
    (g : WFProgram P L)
    (cfg : (syntaxProtocolGraph g).Configuration)
    (hterminal : ¬ cfg.terminal) :
    ∃ node : ProgramNode g.prog,
      node ∈ cfg.frontier ∧
        ∀ other : ProgramNode g.prog,
          other ∈ ProgramNode.finset g.prog →
            (cfg.result other).isNone →
              node.rank ≤ other.rank := by
  rcases ProtocolGraph.Configuration.exists_rank_minimal_ready_of_not_terminal
      (cfg := cfg) hterminal with
    ⟨node, hready, hmin⟩
  refine ⟨node,
    (ProtocolGraph.Configuration.mem_frontier_iff cfg node).mpr hready,
    ?_⟩
  intro other hother hotherUnfinished
  exact hmin other (by
    change other ∈ ProgramNode.finset g.prog
    exact ProgramNode.mem_finset g.prog other)
    hotherUnfinished

end Vegas
