module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphAssembly
public import Vegas.EventGraph.DependencyRelaxation

@[expose] public section

/-! # The compiled graph with relaxed reveal dependencies

Removing direct dependencies between independent reveals preserves source order
for all other event pairs. Sequentialization recovers the source information graph.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The compiled graph of a setup with independent reveals concurrent. -/
abbrev revealRelaxedGraph (setup : Setup (Player := Player) (L := L)) :
    Vegas.EventGraph Player L :=
  setup.dataflowGraph.withDependencies setup.revealDependencies

theorem revealRelaxedGraph_sequentialize (setup : Setup (Player := Player) (L := L)) :
    setup.revealRelaxedGraph.sequentialize = setup.informationGraph := rfl

end Vegas.SourceProgram.Setup
