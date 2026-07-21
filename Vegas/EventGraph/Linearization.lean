/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Confluence

/-!
# Linearizations and the canonical completion

The source semantics fixes a single schedule; the event graph admits many. A
*full order* is any `Nodup` listing of all nodes — a schedule completing the
whole graph. `Vegas.EventGraph.Confluence` already proved completion is
order-independent (`scheduleComplete_perm`); this module packages the
canonical representative and its consequences.

`canonicalCompletion G w` completes the graph from the initial configuration
along the canonical node order `G.nodeOrder`, writing each node the value `w`
assigns it. It is terminal-by-coverage (`canonicalCompletion_terminal`), and
*every* full order reaches it (`scheduleComplete_eq_canonicalCompletion`). The
canonical order is therefore a section of the schedule-free graph: a
distinguished linearization standing in for the source's single schedule, with
all others provably equal to it.

This is store assembly, not a typed execution: `w` may assign each node an
arbitrary `TypedValue`, and the order-independence here holds for *any* `w`. To
model an actual execution `w` must additionally assign each node a value of its
declared type — that coherence is `StoreCoherent.completeNodeTyped`, kept
separate so the order-independence is not entangled with typing.

As a consequence, a player's graph observation at the end is the same whatever
order the graph was scheduled in (`observe_canonicalCompletion_eq`): here the
*whole* terminal configuration is schedule-independent, so the full observation
is too — no readability caveat is needed at the terminal cut.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Graph

/-- A *full order* of a graph: a duplicate-free listing of every node. This is a
schedule that completes the whole graph; by `prereq_lt` the canonical
`nodeOrder` is additionally prerequisite-respecting, but completion is
order-independent regardless. -/
def IsFullOrder (G : Graph Player L) (order : List (Fin G.nodeCount)) : Prop :=
  order.Nodup ∧ ∀ node : Fin G.nodeCount, node ∈ order

/-- The canonical node order is a full order. -/
theorem nodeOrder_isFullOrder (G : Graph Player L) :
    G.IsFullOrder G.nodeOrder :=
  ⟨List.nodup_finRange _, mem_nodeOrder G⟩

end Graph

namespace Config

variable {G : Graph Player L}

/-- The canonical completion: complete the graph from the initial configuration
along the canonical node order, writing each node its assigned value.

This is store assembly — `w` is an arbitrary node-indexed `TypedValue`
assignment and the order-independence results hold for any such `w`. Modelling a
typed execution additionally needs `w` node-typed (cf.
`StoreCoherent.completeNodeTyped`). -/
def canonicalCompletion (G : Graph Player L)
    (w : Fin G.nodeCount → TypedValue L) : Config G :=
  (Config.initial G).scheduleComplete w G.nodeOrder

/-- The canonical completion reaches a terminal configuration (every node is
done). -/
theorem canonicalCompletion_terminal (G : Graph Player L)
    (w : Fin G.nodeCount → TypedValue L) :
    Terminal G (Config.canonicalCompletion G w) :=
  scheduleComplete_terminal w (Graph.mem_nodeOrder G)

/-- Every full order, with the same per-node values, reaches the canonical
completion: completion of the schedule-free graph has a single result, realized
by the canonical linearization. -/
theorem scheduleComplete_eq_canonicalCompletion (G : Graph Player L)
    (w : Fin G.nodeCount → TypedValue L)
    {order : List (Fin G.nodeCount)} (horder : G.IsFullOrder order) :
    (Config.initial G).scheduleComplete w order = Config.canonicalCompletion G w :=
  scheduleComplete_perm (Config.initial G) w
    ((List.perm_ext_iff_of_nodup horder.1 (List.nodup_finRange _)).mpr
      (fun node => ⟨fun _ => Graph.mem_nodeOrder G node, fun _ => horder.2 node⟩))
    horder.1

/-- A player's graph observation at the end of the completion does not depend on
the schedule: all full orders yield the same terminal configuration, hence the
same observation. (At the terminal cut the entire configuration agrees, so this
needs no readability restriction.) -/
theorem observe_canonicalCompletion_eq (G : Graph Player L)
    (w : Fin G.nodeCount → TypedValue L) (who : Player)
    {order : List (Fin G.nodeCount)} (horder : G.IsFullOrder order) :
    observe G ((Config.initial G).scheduleComplete w order) who =
      observe G (Config.canonicalCompletion G w) who :=
  congrArg (fun cfg => observe G cfg who)
    (scheduleComplete_eq_canonicalCompletion G w horder)

end Config

end EventGraph

end Vegas
