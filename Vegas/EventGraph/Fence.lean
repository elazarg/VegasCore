/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.VisibleOrder
import Mathlib.Data.List.Sort

/-!
# Visibility fences and independent reorders

This module grounds the order-side schedule quotient in the graph's dependency
relation. `Graph.Depends` is the transitive closure of the prerequisite
relation — `a` depends on... is required before... `b`. Two nodes are
`Comparable` when one depends on the other, and `Independent` otherwise; the
dependency relation is what a linearization must respect, so exactly the
`Independent` pairs are free to be reordered.

A `Fence who` is the condition that every two distinct nodes both visible to
`who` are `Comparable`: the dependency relation already orders everything `who`
can see. The payoff is `visibleOrder_swap_independent`: under a fence, an
independent transposition — the only reordering a linearization permits — never
moves two `who`-visible nodes past each other, so it leaves `who`'s visible
order unchanged.

This upgrades the raw transposition lemma of `Vegas.EventGraph.VisibleOrder`
(which needed "not both visible" as a hypothesis) to one phrased purely in the
dependency structure. The remaining step toward full schedule-quotient
indistinguishability is global: that any two dependency-respecting linearizations
are connected by independent adjacent transpositions.
-/

namespace Vegas

namespace EventGraph

namespace Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- `a` is required (transitively) before `b`: the transitive closure of the
prerequisite relation. -/
def Depends (G : Graph Player L) (a b : Fin G.nodeCount) : Prop :=
  Relation.TransGen (fun x y => x ∈ G.prereqs y) a b

/-- A dependency points to a strictly earlier node id; in particular `Depends`
is irreflexive. -/
theorem Depends.val_lt {G : Graph Player L} {a b : Fin G.nodeCount}
    (h : G.Depends a b) : (a : Nat) < (b : Nat) := by
  induction h with
  | single hab => exact G.prereq_lt hab
  | tail _hbc hcd ih => exact ih.trans (G.prereq_lt hcd)

theorem Depends.irrefl {G : Graph Player L} (a : Fin G.nodeCount) :
    ¬ G.Depends a a := fun h => (lt_irrefl _ h.val_lt)

/-- Two nodes are comparable when the dependency relation orders them. -/
def Comparable (G : Graph Player L) (a b : Fin G.nodeCount) : Prop :=
  G.Depends a b ∨ G.Depends b a

theorem Comparable.symm {G : Graph Player L} {a b : Fin G.nodeCount}
    (h : G.Comparable a b) : G.Comparable b a := Or.symm h

/-- Two nodes are independent when the dependency relation leaves them unordered
— exactly the pairs a linearization may reorder. -/
def Independent (G : Graph Player L) (a b : Fin G.nodeCount) : Prop :=
  ¬ G.Comparable a b

/-- A *visibility fence* for `who`: every two distinct nodes both visible to
`who` are ordered by the dependency relation. -/
def Fence (G : Graph Player L) (who : Player) : Prop :=
  ∀ ⦃m n : Fin G.nodeCount⦄,
    G.NodeVisibleTo who m → G.NodeVisibleTo who n → m ≠ n → G.Comparable m n

/-- Under a fence, two independent nodes are never both visible to `who`. -/
theorem not_both_visible_of_independent {G : Graph Player L} {who : Player}
    {m n : Fin G.nodeCount}
    (hfence : G.Fence who) (hindep : G.Independent m n) (hmn : m ≠ n) :
    ¬ (G.NodeVisibleTo who m ∧ G.NodeVisibleTo who n) := by
  rintro ⟨hvm, hvn⟩
  exact hindep (hfence hvm hvn hmn)

/-- **Independent reorders are invisible under a fence.** Transposing two
adjacent independent nodes leaves `who`'s visible order unchanged: a fence
forbids two independent nodes from both being visible, so the only reorderings a
linearization permits are exactly the `who`-invisible ones. -/
theorem visibleOrder_swap_independent {G : Graph Player L} (who : Player)
    {m n : Fin G.nodeCount} (rest : List (Fin G.nodeCount))
    (hfence : G.Fence who) (hindep : G.Independent m n) (hmn : m ≠ n) :
    G.visibleOrder who (m :: n :: rest) =
      G.visibleOrder who (n :: m :: rest) :=
  visibleOrder_swap_of_not_both G who rest
    (not_both_visible_of_independent hfence hindep hmn)

/-! ## Global schedule-quotient invariance -/

/-- A *linearization*: a dependency-respecting full order, in which no node
appears before something that is required before it. -/
def IsTopo (G : Graph Player L) (order : List (Fin G.nodeCount)) : Prop :=
  order.Nodup ∧ (∀ node : Fin G.nodeCount, node ∈ order) ∧
    order.Pairwise fun a b => ¬ G.Depends b a

/-- Under a fence, a player's visible projection of any linearization is sorted
by node id: dependency orders all visible nodes, and dependencies increase the
id. -/
theorem visibleOrder_sorted_of_fence {G : Graph Player L} {who : Player}
    {order : List (Fin G.nodeCount)}
    (htopo : G.IsTopo order) (hfence : G.Fence who) :
    (G.visibleOrder who order).Pairwise (· < ·) := by
  have hcond :
      order.Pairwise fun a b =>
        G.NodeVisibleTo who a → G.NodeVisibleTo who b → a < b := by
    refine (htopo.2.2.and htopo.1).imp ?_
    rintro a b ⟨hndep, hne⟩ hva hvb
    rcases hfence hva hvb hne with hdab | hdba
    · exact Fin.lt_def.mpr hdab.val_lt
    · exact absurd hdba hndep
  have hsub :
      (G.visibleOrder who order).Pairwise fun a b =>
        G.NodeVisibleTo who a → G.NodeVisibleTo who b → a < b :=
    List.Pairwise.sublist List.filter_sublist hcond
  exact hsub.imp_of_mem fun {a b} ha hb hr =>
    hr (by simpa using List.of_mem_filter ha) (by simpa using List.of_mem_filter hb)

/-- **Schedule-quotient indistinguishability.** Under a visibility fence, every
linearization presents `who` the same visible order. The schedule is below the
player's order view: reorderings the dependency relation permits are exactly the
ones `who` cannot see. -/
theorem visibleOrder_eq_of_fence {G : Graph Player L} {who : Player}
    {o₁ o₂ : List (Fin G.nodeCount)}
    (h₁ : G.IsTopo o₁) (h₂ : G.IsTopo o₂) (hfence : G.Fence who) :
    G.visibleOrder who o₁ = G.visibleOrder who o₂ := by
  haveI : Std.Irrefl (α := Fin G.nodeCount) (· < ·) := ⟨fun a => lt_irrefl a⟩
  refine List.Pairwise.eq_of_mem_iff
    (visibleOrder_sorted_of_fence h₁ hfence)
    (visibleOrder_sorted_of_fence h₂ hfence) fun a => ?_
  simp only [visibleOrder, List.mem_filter, h₁.2.1 a, h₂.2.1 a, true_and]

end Graph

end EventGraph

end Vegas
