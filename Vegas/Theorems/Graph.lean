/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceBridge

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

/-- The checked program's compiled graph preserves the source order skeleton at
the owner/readability level: reading node owners along canonical graph order is
the source order trace projected to graph node owners. -/
theorem compiledGraph_nodeOrder_owners_eq_sourceOrderTrace_graphOwners
    (program : WFProgram P L) (who : P) :
    (((ToEventGraph.compile program.core).graph.nodeOrder.map
        fun node => ((ToEventGraph.compile program.core).graph.nodeRow node).owner)) =
      (program.core.prog.orderTrace who).map
        SourcePlayerEvent.Kind.graphOwner :=
  ToEventGraph.compile_graph_nodeOrder_owners_eq_orderTrace_graphOwners
    program.core who

/-- The checked program's compiled graph preserves the source order skeleton at
the per-player readable-output level: the canonical graph readable-owner order
is the source order trace projected to graph node owners, then restricted to
values readable by `who`. -/
theorem compiledGraph_readableOrder_owners_eq_sourceOrderTrace_readableGraphOwners
    (program : WFProgram P L) (who : P) :
    ((((ToEventGraph.compile program.core).graph.readableOrder who
        (ToEventGraph.compile program.core).graph.nodeOrder).map
        fun node => ((ToEventGraph.compile program.core).graph.nodeRow node).owner)) =
      ((program.core.prog.orderTrace who).map
        SourcePlayerEvent.Kind.graphOwner).filter
          fun owner => decide (owner = none ∨ owner = some who) :=
  ToEventGraph.compile_graph_readableOrder_owners_eq_orderTrace_readableGraphOwners
    program.core who

end WFProgram

end Vegas
