/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Confluence

/-!
# Linearizations and the canonical execution

The source semantics fixes a single schedule; the event graph admits many. A
*full order* is any `Nodup` listing of all nodes — a schedule completing the
whole graph. `Vegas.EventGraph.Confluence` already proved completion is
order-independent (`scheduleComplete_eq_of_full`); this module packages the
canonical representative and its consequences.

`runComplete G w` runs the graph from the initial configuration along the
canonical node order `G.nodeOrder` with the value assignment `w`. It is terminal
(`runComplete_terminal`), and *every* full order reaches it
(`scheduleComplete_eq_runComplete`). The canonical order is therefore a section
of the schedule-free graph: a distinguished linearization standing in for the
source's single schedule, with all others provably equal to it.

As a per-player consequence, a player's interim graph observation at the end of
the run is the same whatever order the graph was scheduled in
(`observe_runComplete_eq`): the schedule is below the player's terminal view.
This is the outcome-level half of interim-view invariance; the finer per-cut
order invariance needs a visibility fence and is left to a later development.
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

/-- The canonical execution: complete the graph from the initial configuration
along the canonical node order, writing each node its assigned value. -/
def runComplete (G : Graph Player L) (w : Fin G.nodeCount → TypedValue L) :
    Config G :=
  (Config.initial G).scheduleComplete w G.nodeOrder

/-- The canonical execution reaches a terminal configuration. -/
theorem runComplete_terminal (G : Graph Player L)
    (w : Fin G.nodeCount → TypedValue L) :
    Terminal G (Config.runComplete G w) :=
  scheduleComplete_terminal w (Graph.mem_nodeOrder G)

/-- Every full order, with the same per-node values, reaches the canonical
execution: the schedule-free graph has a single outcome, realized by the
canonical linearization. -/
theorem scheduleComplete_eq_runComplete (G : Graph Player L)
    (w : Fin G.nodeCount → TypedValue L)
    {order : List (Fin G.nodeCount)} (horder : G.IsFullOrder order) :
    (Config.initial G).scheduleComplete w order = Config.runComplete G w :=
  scheduleComplete_perm (Config.initial G) w
    ((List.perm_ext_iff_of_nodup horder.1 (List.nodup_finRange _)).mpr
      (fun node => ⟨fun _ => Graph.mem_nodeOrder G node, fun _ => horder.2 node⟩))
    horder.1

/-- A player's graph observation at the end of the run does not depend on the
schedule: all full orders yield the same terminal configuration, hence the same
observation. -/
theorem observe_runComplete_eq (G : Graph Player L)
    (w : Fin G.nodeCount → TypedValue L) (who : Player)
    {order : List (Fin G.nodeCount)} (horder : G.IsFullOrder order) :
    observe G ((Config.initial G).scheduleComplete w order) who =
      observe G (Config.runComplete G w) who :=
  congrArg (fun cfg => observe G cfg who)
    (scheduleComplete_eq_runComplete G w horder)

end Config

end EventGraph

end Vegas
