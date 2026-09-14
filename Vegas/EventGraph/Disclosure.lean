/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Basic

/-! # Direct disclosure uniqueness

Each field has at most one direct reveal node. This is an additional graph
condition, independent of well-formedness and declared information. It lets a
defaulted public disclosure be represented by one changed commitment value
without contradicting another disclosure of the same field.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A field is directly disclosed at most once in the graph. -/
def Graph.UniqueReveals (G : Graph Player L) : Prop :=
  ∀ (left right : Fin G.nodeCount) (field : Nat),
    (G.nodeRow left).sem = .reveal field →
    (G.nodeRow right).sem = .reveal field → left = right

end Vegas.EventGraph
