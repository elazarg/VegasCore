import Vegas.Protocol.ProgramEventGraph

/-!
# Syntax-linear reading of event graphs

This file gives a small formal version of the programmer-facing reading
principle: source syntax may be read as a straight-line protocol order without
getting stuck. The executable semantics remains event-graph/machine-native; the
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

/-- Source-linear order is topological for the compiled event graph:
every event-graph prerequisite has smaller source rank than the node that
reads it.

This is the static reason that a straight-line reading is sufficient. -/
theorem syntaxLinearRead_prereq_rank_lt
    (g : WFProgram P L)
    {node prereq : ProgramNode g.prog}
    (hpre : prereq ∈ (programEventGraph g).prereqs node) :
    prereq.rank < node.rank :=
  (programEventGraph g).prereq_rank_lt
    (by
      change node ∈ ProgramNode.finset g.prog
      exact ProgramNode.mem_finset g.prog node) hpre

/-- If a node is the first unfinished source node by source rank, then it is
on the event-graph frontier.

This is the local "linear read is sufficient" theorem: the reader can scan the
source-order nodes, stop at the first one not yet executed, and that node is a
legal next event whenever the event graph has not terminated. -/
theorem syntaxLinearRead_rank_minimal_unfinished_mem_frontier
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration)
    {node : ProgramNode g.prog}
    (hunfinished : (cfg.result node).isNone)
    (hmin :
      ∀ other : ProgramNode g.prog,
        other ∈ ProgramNode.finset g.prog →
          (cfg.result other).isNone →
            node.rank ≤ other.rank) :
    node ∈ cfg.frontier := by
  exact (EventGraph.Configuration.mem_frontier_iff cfg node).mpr <|
    cfg.enabled_of_rank_minimal_unfinished
    (by
      change node ∈ ProgramNode.finset g.prog
      exact ProgramNode.mem_finset g.prog node)
    hunfinished
    (by
      intro other hother hotherUnfinished
      exact hmin other (ProgramNode.mem_finset g.prog other)
        hotherUnfinished)

/-- Every nonterminal event graph has a frontier node that is earliest among
unfinished source nodes.

Thus the straight-line/source-rank presentation never gets stuck before the
event-graph machine semantics does. -/
theorem syntaxLinearRead_sufficient
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration)
    (hterminal : ¬ cfg.terminal) :
    ∃ node : ProgramNode g.prog,
      node ∈ cfg.frontier ∧
        ∀ other : ProgramNode g.prog,
          other ∈ ProgramNode.finset g.prog →
            (cfg.result other).isNone →
              node.rank ≤ other.rank := by
  rcases EventGraph.Configuration.exists_rank_minimal_enabled_of_not_terminal
      (cfg := cfg) hterminal with
    ⟨node, henabled, hmin⟩
  refine ⟨node,
    (EventGraph.Configuration.mem_frontier_iff cfg node).mpr henabled,
    ?_⟩
  intro other hother hotherUnfinished
  exact hmin other (by
    change other ∈ ProgramNode.finset g.prog
    exact ProgramNode.mem_finset g.prog other)
    hotherUnfinished

end Vegas
