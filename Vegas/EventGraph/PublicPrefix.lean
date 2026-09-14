/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Basic

/-! # Declared access to earlier public graph outputs

Well-formedness validates the fields a decision declares. Public-prefix
readability additionally requires its declaration to include every earlier
public node output. This information condition is independent of source syntax,
runtime scheduling, commitment services, and utilities.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Decisions may read every public output preceding them in the graph's
canonical node order. This is an additional information condition, not graph WF. -/
def Graph.PublicPrefixReadable (G : Graph Player L) : Prop :=
  ∀ (who : Player) (decision prior : Fin G.nodeCount) (guard : EventGuard L),
    (G.nodeRow decision).sem = .commit who guard → prior.val < decision.val →
    (G.nodeRow prior).owner = none →
    { field := G.nodeTarget prior, ty := (G.nodeRow prior).ty } ∈ guard.choiceReads

end Vegas.EventGraph
