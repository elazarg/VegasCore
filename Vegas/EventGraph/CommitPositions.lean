/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Basic
import Mathlib.Data.List.Nodup

/-! # Commitment coordinates of an event graph

Strategic sites are indexed by their controller and canonical node number.
The list has no duplicates and supports finite products without referring to
source syntax or runtime message identities.
-/

namespace Vegas.EventGraph.Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} (G : Graph Player L)

/-- Controller/node coordinates of all graph commitment sites in node order. -/
def commitPositions : List (Player × Nat) :=
  G.nodeOrder.filterMap fun node => (G.nodeRow node).sem.actor.map (fun who => (who, node.val))

theorem mem_commitPositions (who : Player) (slot : Nat) :
    (who, slot) ∈ G.commitPositions ↔
      ∃ node : Fin G.nodeCount, ∃ guard : EventGuard L,
        (G.nodeRow node).sem = .commit who guard ∧ node.val = slot := by
  simp only [commitPositions, List.mem_filterMap, G.mem_nodeOrder, true_and]
  constructor
  · rintro ⟨node, hnode⟩
    cases hsem : (G.nodeRow node).sem with
    | commit owner guard =>
        simp only [hsem, NodeSem.actor, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnode
        obtain ⟨rfl, hslot⟩ := hnode
        exact ⟨node, guard, hsem, hslot⟩
    | sample dist | reveal source => simp [hsem, NodeSem.actor] at hnode
  · rintro ⟨node, guard, hsem, hslot⟩
    exact ⟨node, by simp [hsem, NodeSem.actor, hslot]⟩

theorem commitPositions_nodup : G.commitPositions.Nodup := by
  apply List.Nodup.filterMap ?_ G.nodeOrder_nodup
  intro left right handle hleft hright
  obtain ⟨who, _, hwho⟩ := Option.map_eq_some_iff.mp hleft
  obtain ⟨other, _, hother⟩ := Option.map_eq_some_iff.mp hright
  apply Fin.ext
  exact congrArg Prod.snd (hwho.trans hother.symm)

/-- Products over strategic coordinates equal node products with unit
factors at internal nodes. -/
theorem prod_commitPositions {M : Type*} [Monoid M] (factor : Player → Nat → M) :
    (G.commitPositions.map fun slot => factor slot.1 slot.2).prod =
      (G.nodeOrder.map fun node => match (G.nodeRow node).sem with
        | .commit who _ => factor who node.val
        | _ => 1).prod := by
  unfold commitPositions
  generalize G.nodeOrder = order
  induction order with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.filterMap_cons, List.map_cons, List.prod_cons]
      simp only [NodeSem.actor] at ih
      cases hsem : (G.nodeRow node).sem <;>
        simp only [NodeSem.actor, Option.map_none, Option.map_some, List.map_cons,
          List.prod_cons, one_mul] <;>
        rw [ih]

end Vegas.EventGraph.Graph
