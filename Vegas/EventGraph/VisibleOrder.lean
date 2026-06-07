/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-!
# Readable-output order and reordering

A linearization orders all graph nodes; different linearizations differ by
reordering nodes the dependency relation leaves free. This module is the
order/occurrence side of interim-view invariance, restricted to one specific
projection: the order in which a player's *readable values* appear.

`Graph.NodeOutputReadableBy who` holds when a node's output field is public or
owned by `who` — i.e. `who` may read its value. `Graph.readableOrder who`
projects a node order to the subsequence of such nodes. This is *not* the
player's full observation surface: event occurrences are public (the source view
exposes another player's commit as `otherCommit`, and the graph exposes completed
nodes via `done`), so the order of *all* nodes is observable and is genuinely
schedule-dependent. What this module tracks is narrower — the relative order of
the values `who` can actually read.

The key fact `readableOrder_swap_of_not_both` is the local invariance: transposing
two adjacent nodes, at least one of whose output `who` cannot read, leaves `who`'s
readable-output order unchanged. `Vegas.EventGraph.Fence` upgrades this to a
global statement under a readability fence.
-/

namespace Vegas

namespace EventGraph

namespace Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- `who` can read a node's output value: its output field is public or owned by
`who`. Note this is about reading the value, not observing the occurrence — every
node's occurrence is public. -/
def NodeOutputReadableBy (G : Graph Player L) (who : Player)
    (node : Fin G.nodeCount) : Prop :=
  (G.nodeRow node).owner = none ∨ (G.nodeRow node).owner = some who

instance (G : Graph Player L) (who : Player) (node : Fin G.nodeCount) :
    Decidable (G.NodeOutputReadableBy who node) := by
  unfold NodeOutputReadableBy
  infer_instance

/-- Player `who`'s readable-output order for a node order: the subsequence of
nodes whose output value `who` can read. -/
def readableOrder (G : Graph Player L) (who : Player)
    (order : List (Fin G.nodeCount)) : List (Fin G.nodeCount) :=
  order.filter fun node => decide (G.NodeOutputReadableBy who node)

@[simp] theorem readableOrder_nil (G : Graph Player L) (who : Player) :
    G.readableOrder who [] = [] := rfl

/-- **Local invariance of the readable-output order.** Transposing two adjacent
nodes, at least one whose output `who` cannot read, does not change `who`'s
readable-output order. -/
theorem readableOrder_swap_of_not_both
    (G : Graph Player L) (who : Player)
    {m n : Fin G.nodeCount} (rest : List (Fin G.nodeCount))
    (h : ¬ (G.NodeOutputReadableBy who m ∧ G.NodeOutputReadableBy who n)) :
    G.readableOrder who (m :: n :: rest) =
      G.readableOrder who (n :: m :: rest) := by
  unfold readableOrder
  by_cases hm : G.NodeOutputReadableBy who m
  · by_cases hn : G.NodeOutputReadableBy who n
    · exact absurd ⟨hm, hn⟩ h
    · simp [hm, hn]
  · simp [List.filter_cons, hm]

end Graph

end EventGraph

end Vegas
