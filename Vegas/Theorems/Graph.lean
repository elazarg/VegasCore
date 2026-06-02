import Vegas.Compile.Compiler

/-!
# Compiled graph facts

The graph theorem surface exposes the validity facts carried by the compiler:
compiled graphs are well formed, payoff projections read public terminal data,
and checked-program legality gives guard liveness.
-/

namespace Vegas

namespace ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Graph programs compile to well-formed event graphs. -/
theorem compile_graph_wf (program : GraphProgram P L) :
    (compile program).graph.WF :=
  (compile program).graphWF

/-- Compiled payoff projections read public fields available at terminality. -/
theorem compile_payoffs_wf
    (program : GraphProgram P L) :
    ∀ payoff, payoff ∈ (compile program).payoffs →
      ∀ ref, ref ∈ payoff.2.reads →
        (compile program).graph.fieldRefPublic ref ∧
        (compile program).graph.fieldAvailableBefore
            (compile program).graph.nodeCount ref.field = true :=
  (compile program).payoffsWF

/-- Checked source guard legality compiles to graph-level guard liveness. -/
theorem compile_graph_guard_live
    (program : WFProgram P L) :
    EventGraph.GuardLive (compile program.core).graph :=
  compile_guardLive program

end ToEventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The checked program's compiled graph is well formed. -/
theorem compiledGraph_wf (program : WFProgram P L) :
    (ToEventGraph.compile program.core).graph.WF :=
  ToEventGraph.compile_graph_wf program.core

/-- The checked program's compiled payoff projection is well formed. -/
theorem compiledPayoffs_wf
    (program : WFProgram P L) :
    ∀ payoff, payoff ∈ (ToEventGraph.compile program.core).payoffs →
      ∀ ref, ref ∈ payoff.2.reads →
        (ToEventGraph.compile program.core).graph.fieldRefPublic ref ∧
        (ToEventGraph.compile program.core).graph.fieldAvailableBefore
            (ToEventGraph.compile program.core).graph.nodeCount ref.field =
          true :=
  ToEventGraph.compile_payoffs_wf program.core

/-- The checked program's compiled commit guards are live. -/
theorem compiledGraph_guardLive (program : WFProgram P L) :
    EventGraph.GuardLive (ToEventGraph.compile program.core).graph :=
  ToEventGraph.compile_graph_guard_live program

end WFProgram

end Vegas
