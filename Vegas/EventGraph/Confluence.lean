/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Execution

/-!
# Confluent coarsening of the event graph

The small-step semantics fixes a single schedule (see `Vegas.Core.Schedule`).
The event graph deliberately does *not*: `EventGraph.Execution` exposes available
events without choosing an order. This module justifies that move at the level
of the raw graph configuration.

A *schedule* is an order in which nodes are completed. `Config.completeNodes`
folds a list of `(node, value)` writes in that order, and `Config.scheduleComplete`
specialises to a fixed per-node value assignment. The headline results are:

* `completeNodes_perm` / `scheduleComplete_perm` — **conservativity**: permuting
  the schedule (with the per-node values held fixed) does not change the
  resulting configuration. This is the diamond `completeNode_comm` closed under
  arbitrary reordering, i.e. the order-independence at the heart of the
  confluent-coarsening picture.
* `scheduleComplete_eq_of_full` — any two schedules that complete *all* nodes
  yield the *same* terminal configuration: the outcome is a function of the
  values alone, with the schedule a vacuous argument.
* `card_completeNode_of_not_mem` / `card_done_le` — the termination measure
  (completed-node count strictly increases, bounded by `nodeCount`) that makes
  the rewrite system strongly normalising, so local confluence suffices.

This is the unconditional, outcome-level half of the justification. Lifting it
to *per-player views* at intermediate cuts is a separate, finer obligation.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Config

variable {G : Graph Player L}

/-! ## Completing a schedule -/

/-- Complete a list of `(node, value)` writes left to right. A *schedule* is the
order of this list; `completeNodes` realises the writes in that order. -/
def completeNodes (cfg : Config G)
    (steps : List (Fin G.nodeCount × TypedValue L)) : Config G :=
  steps.foldl (fun c s => c.completeNode s.1 s.2) cfg

@[simp] theorem completeNodes_nil (cfg : Config G) :
    cfg.completeNodes [] = cfg := rfl

@[simp] theorem completeNodes_cons (cfg : Config G)
    (s : Fin G.nodeCount × TypedValue L)
    (rest : List (Fin G.nodeCount × TypedValue L)) :
    cfg.completeNodes (s :: rest) =
      (cfg.completeNode s.1 s.2).completeNodes rest := rfl

/-- The completed-node set after a schedule is the original set together with
every node the schedule touched, regardless of order. -/
theorem completeNodes_done (cfg : Config G)
    (steps : List (Fin G.nodeCount × TypedValue L)) :
    (cfg.completeNodes steps).done =
      cfg.done ∪ (steps.map Prod.fst).toFinset := by
  induction steps generalizing cfg with
  | nil => simp
  | cons s rest ih =>
      rw [completeNodes_cons, ih]
      simp [Config.completeNode, List.toFinset_cons, Finset.insert_union,
        Finset.union_insert]

/-! ## Termination measure -/

/-- Completing a fresh node grows the done-set by exactly one. -/
theorem card_completeNode_of_not_mem (cfg : Config G)
    {node : Fin G.nodeCount} (value : TypedValue L)
    (h : node ∉ cfg.done) :
    (cfg.completeNode node value).done.card = cfg.done.card + 1 := by
  simp [Config.completeNode, Finset.card_insert_of_notMem h]

/-- Completing a node only ever adds to the done-set. -/
theorem done_subset_completeNode (cfg : Config G)
    (node : Fin G.nodeCount) (value : TypedValue L) :
    cfg.done ⊆ (cfg.completeNode node value).done := by
  simp [Config.completeNode, Finset.subset_insert]

/-- The done-set never has more than `nodeCount` elements: the rewrite system is
strongly normalising. -/
theorem card_done_le (cfg : Config G) : cfg.done.card ≤ G.nodeCount :=
  calc cfg.done.card
      ≤ (Finset.univ : Finset (Fin G.nodeCount)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = G.nodeCount := Finset.card_fin _

/-! ## Conservativity: schedules commute -/

/-- **Conservativity of the coarsening.** Permuting the schedule, with the
per-node values held fixed, leaves the resulting configuration unchanged. The
distinctness hypothesis (the touched nodes are `Nodup`) is what licenses each
transposition via the `completeNode` diamond. -/
theorem completeNodes_perm (cfg : Config G)
    {steps₁ steps₂ : List (Fin G.nodeCount × TypedValue L)}
    (hperm : List.Perm steps₁ steps₂) :
    (steps₁.map Prod.fst).Nodup →
      cfg.completeNodes steps₁ = cfg.completeNodes steps₂ := by
  induction hperm generalizing cfg with
  | nil => intro _; rfl
  | cons s _p ih =>
      intro hnodup
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [completeNodes_cons]
      exact ih (cfg.completeNode s.1 s.2) hnodup.2
  | swap s t l =>
      intro hnodup
      simp only [List.map_cons] at hnodup
      have hne : t.1 ≠ s.1 := by
        intro heq
        apply (List.nodup_cons.mp hnodup).1
        rw [heq]
        exact List.mem_cons_self
      simp only [completeNodes_cons]
      rw [Config.completeNode_comm cfg (left := t.1) (right := s.1) t.2 s.2 hne]
  | trans p₁ _p₂ ih₁ ih₂ =>
      intro hnodup
      exact (ih₁ cfg hnodup).trans
        (ih₂ cfg ((p₁.map Prod.fst).nodup_iff.mp hnodup))

/-! ## A fixed value assignment scheduled in any order -/

/-- Complete the nodes listed in `order`, writing each its assigned value `w`. -/
def scheduleComplete (cfg : Config G) (w : Fin G.nodeCount → TypedValue L)
    (order : List (Fin G.nodeCount)) : Config G :=
  cfg.completeNodes (order.map (fun node => (node, w node)))

/-- The nodes touched by `scheduleComplete w order` are exactly `order`. -/
@[simp] theorem map_fst_pair (order : List (Fin G.nodeCount))
    (w : Fin G.nodeCount → TypedValue L) :
    (order.map (fun node => (node, w node))).map Prod.fst = order := by
  induction order with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem scheduleComplete_done (cfg : Config G)
    (w : Fin G.nodeCount → TypedValue L) (order : List (Fin G.nodeCount)) :
    (cfg.scheduleComplete w order).done = cfg.done ∪ order.toFinset := by
  unfold scheduleComplete
  rw [completeNodes_done, map_fst_pair]

/-- **Schedule-invariance for a fixed value assignment.** Two orderings of the
same node set, completing each node with the same value, reach the same
configuration. -/
theorem scheduleComplete_perm (cfg : Config G)
    (w : Fin G.nodeCount → TypedValue L)
    {o₁ o₂ : List (Fin G.nodeCount)}
    (hperm : List.Perm o₁ o₂) (hnodup : o₁.Nodup) :
    cfg.scheduleComplete w o₁ = cfg.scheduleComplete w o₂ := by
  unfold scheduleComplete
  refine completeNodes_perm cfg (hperm.map _) ?_
  rw [map_fst_pair]
  exact hnodup

/-- A schedule that lists every node drives the initial configuration to a
terminal one. -/
theorem scheduleComplete_terminal (w : Fin G.nodeCount → TypedValue L)
    {order : List (Fin G.nodeCount)} (hcover : ∀ node, node ∈ order) :
    Terminal G ((Config.initial G).scheduleComplete w order) := by
  intro node
  rw [scheduleComplete_done]
  simp only [Config.initial, Finset.empty_union, List.mem_toFinset]
  exact hcover node

/-- **Outcome confluence.** Any two schedules that complete *all* nodes, writing
each node the same value, yield the *same* terminal configuration. The terminal
configuration is a function of the value assignment alone; the schedule is a
vacuous argument. -/
theorem scheduleComplete_eq_of_full (cfg : Config G)
    (w : Fin G.nodeCount → TypedValue L)
    {o₁ o₂ : List (Fin G.nodeCount)}
    (h₁ : o₁.Nodup) (h₂ : o₂.Nodup)
    (c₁ : ∀ node, node ∈ o₁) (c₂ : ∀ node, node ∈ o₂) :
    cfg.scheduleComplete w o₁ = cfg.scheduleComplete w o₂ :=
  scheduleComplete_perm cfg w
    ((List.perm_ext_iff_of_nodup h₁ h₂).mpr
      (fun a => ⟨fun _ => c₂ a, fun _ => c₁ a⟩)) h₁

end Config

end EventGraph

end Vegas
