/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-!
# Player-visible order and the schedule quotient

A linearization orders all graph nodes; different linearizations differ by
reordering nodes the dependency relation leaves free. This module is the
order/occurrence side of interim-view invariance: it asks when such reorderings
are invisible to a player.

`Graph.visibleOrder who` projects a node order to the subsequence of nodes whose
event is visible to `who` (public, or owned by `who`). The key fact
`visibleOrder_swap_of_not_both` is the local invariance: transposing two adjacent
nodes, at least one of which `who` cannot see, leaves `who`'s visible order
unchanged. This is the order-side reading of the `Unit`-not-`Option-Unit`
picture — a reorder that moves an invisible event past its neighbour cannot be
observed.

A *visibility fence* for `who` is the condition that any two `who`-visible nodes
are ordered by the dependency relation (never independent). Under the fence, two
nodes left free to reorder are never both visible, so every independent
transposition is `who`-invisible — and since any two dependency-respecting
linearizations are connected by independent transpositions, `who`'s visible
order is a schedule invariant. The per-transposition step is proved here; the
global connectivity that assembles it into full schedule-quotient
indistinguishability is left to a later development.
-/

namespace Vegas

namespace EventGraph

namespace Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A node's event is visible to `who` when its output field is public or owned
by `who`. -/
def NodeVisibleTo (G : Graph Player L) (who : Player)
    (node : Fin G.nodeCount) : Prop :=
  (G.nodeRow node).owner = none ∨ (G.nodeRow node).owner = some who

instance (G : Graph Player L) (who : Player) (node : Fin G.nodeCount) :
    Decidable (G.NodeVisibleTo who node) := by
  unfold NodeVisibleTo
  infer_instance

/-- Player `who`'s view of a node order: the subsequence of nodes whose event
`who` can see. -/
def visibleOrder (G : Graph Player L) (who : Player)
    (order : List (Fin G.nodeCount)) : List (Fin G.nodeCount) :=
  order.filter fun node => decide (G.NodeVisibleTo who node)

@[simp] theorem visibleOrder_nil (G : Graph Player L) (who : Player) :
    G.visibleOrder who [] = [] := rfl

/-- **Local schedule-quotient invariance.** Transposing two adjacent nodes, at
least one invisible to `who`, does not change `who`'s visible order. An
independent reorder that moves an unobservable event past its neighbour is
invisible to the player. -/
theorem visibleOrder_swap_of_not_both
    (G : Graph Player L) (who : Player)
    {m n : Fin G.nodeCount} (rest : List (Fin G.nodeCount))
    (h : ¬ (G.NodeVisibleTo who m ∧ G.NodeVisibleTo who n)) :
    G.visibleOrder who (m :: n :: rest) = G.visibleOrder who (n :: m :: rest) := by
  unfold visibleOrder
  by_cases hm : G.NodeVisibleTo who m
  · by_cases hn : G.NodeVisibleTo who n
    · exact absurd ⟨hm, hn⟩ h
    · simp [hm, hn]
  · simp [List.filter_cons, hm]

end Graph

end EventGraph

end Vegas
