/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.VisibleOrder
import Mathlib.Data.List.Sort

/-!
# Readability fences and independent reorders

This module grounds the readable-output order quotient in the graph's dependency
relation. `Graph.Depends` is the transitive closure of the prerequisite
relation — `a` is required before `b`. Two nodes are `Comparable` when one
depends on the other, and `Independent` otherwise; a linearization must respect
the dependency relation, so exactly the `Independent` pairs are free to be
reordered.

A `Fence who` is the condition that every two distinct nodes both *readable* by
`who` (whose output `who` may read, `NodeOutputReadableBy`) are `Comparable`: the
dependency relation already orders everything `who` can read. The payoff is
`readableOrder_eq_of_fence`: under a fence, every linearization presents `who` the
same readable-output order.

A caveat on scope, carried over from `Vegas.EventGraph.VisibleOrder`: this is the
order of the *values* `who` can read, not `who`'s full observation. Event
occurrences are public, so the order of all nodes is itself observable and
schedule-dependent; the fence makes only the readable-value projection a schedule
invariant. The remaining step toward a statement about `who`'s complete observed
trace would have to model occurrence observations as well.
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

/-! ### Deciding the dependency relation

`Depends` is a transitive closure, which Mathlib gives no decidability instance
for.  It is nevertheless decidable here, because prerequisites point strictly
backwards (`prereq_lt`): a dependency chain ending at `b` has fewer than
`b + 1` edges, so bounded search at that depth is complete.  Making this
decidable is what lets `Fence` be *checked* for a given graph rather than
merely assumed. -/

/-- `a` reaches `b` through at most `fuel` prerequisite edges. -/
def DependsWithin (G : Graph Player L) :
    Nat → Fin G.nodeCount → Fin G.nodeCount → Prop
  | 0, _, _ => False
  | fuel + 1, a, b =>
      a ∈ G.prereqs b ∨ ∃ c ∈ G.prereqs b, G.DependsWithin fuel a c

instance instDecidableDependsWithin (G : Graph Player L) :
    ∀ (fuel : Nat) (a b : Fin G.nodeCount), Decidable (G.DependsWithin fuel a b)
  | 0, _, _ => isFalse (by simp [DependsWithin])
  | fuel + 1, a, b => by
      letI : ∀ c : Fin G.nodeCount, Decidable (G.DependsWithin fuel a c) :=
        fun c => instDecidableDependsWithin G fuel a c
      unfold DependsWithin
      infer_instance

/-- Bounded reachability only improves with more fuel. -/
theorem DependsWithin.mono {G : Graph Player L} {a b : Fin G.nodeCount}
    {fuel : Nat} :
    ∀ {bound : Nat}, fuel ≤ bound → G.DependsWithin fuel a b →
      G.DependsWithin bound a b := by
  induction fuel generalizing b with
  | zero => intro _ _ h; exact absurd h (by simp [DependsWithin])
  | succ fuel ih =>
      intro bound hle h
      obtain ⟨bound, rfl⟩ : ∃ k, bound = k + 1 :=
        ⟨bound - 1, by omega⟩
      rcases h with hdirect | ⟨c, hc, hrest⟩
      · exact Or.inl hdirect
      · exact Or.inr ⟨c, hc, ih (by omega) hrest⟩

/-- Bounded reachability is a dependency. -/
theorem Depends.of_dependsWithin {G : Graph Player L} {a b : Fin G.nodeCount} :
    ∀ {fuel : Nat}, G.DependsWithin fuel a b → G.Depends a b := by
  intro fuel
  induction fuel generalizing b with
  | zero => intro h; exact absurd h (by simp [DependsWithin])
  | succ fuel ih =>
      intro h
      rcases h with hdirect | ⟨c, hc, hrest⟩
      · exact Relation.TransGen.single hdirect
      · exact Relation.TransGen.tail (ih hrest) hc

/-- A dependency is found by bounded search at depth `b + 1`: prerequisites
point strictly backwards, so no chain ending at `b` is longer than that. -/
theorem Depends.dependsWithin {G : Graph Player L} {a b : Fin G.nodeCount}
    (h : G.Depends a b) : G.DependsWithin ((b : Nat) + 1) a b := by
  induction h with
  | single hab => exact Or.inl hab
  | @tail b c _hab hbc ih =>
      refine Or.inr ⟨b, hbc, ?_⟩
      exact DependsWithin.mono (by have := G.prereq_lt hbc; omega) ih

/-- `Depends` is decided by bounded search at the graph's node count. -/
theorem depends_iff_dependsWithin (G : Graph Player L)
    (a b : Fin G.nodeCount) :
    G.Depends a b ↔ G.DependsWithin G.nodeCount a b := by
  constructor
  · intro h
    exact DependsWithin.mono (by omega) h.dependsWithin
  · exact Depends.of_dependsWithin

instance instDecidableDepends (G : Graph Player L) (a b : Fin G.nodeCount) :
    Decidable (G.Depends a b) :=
  decidable_of_iff _ (G.depends_iff_dependsWithin a b).symm

/-- Two nodes are independent when the dependency relation leaves them unordered
— exactly the pairs a linearization may reorder. -/
def Independent (G : Graph Player L) (a b : Fin G.nodeCount) : Prop :=
  ¬ G.Comparable a b

/-- A *readability fence* for `who`: every two distinct nodes both readable by
`who` are ordered by the dependency relation.

Operationally, a fence is the developer's **ordering knob** (a `barrier` in
true-concurrency terms): it promotes incidental program order into
strategically-real *partial-order* dependency for `who`. The presence or absence
of a fence is the seam between **plain and strong linearizability** of `who`'s
readable information — see `readableOrder_eq_of_fence`. -/
def Fence (G : Graph Player L) (who : Player) : Prop :=
  ∀ ⦃m n : Fin G.nodeCount⦄,
    G.NodeOutputReadableBy who m → G.NodeOutputReadableBy who n → m ≠ n →
      G.Comparable m n

instance instDecidableComparable (G : Graph Player L) (a b : Fin G.nodeCount) :
    Decidable (G.Comparable a b) := by
  unfold Comparable
  infer_instance

/-- A fence is a *checkable* property of a graph, not a universal one: a player
who can read two dependency-independent nodes does not have one.  It therefore
belongs with the other per-program preconditions, and this instance is what
lets a compiler or a test decide it for a concrete graph. -/
instance instDecidableFence (G : Graph Player L) (who : Player) :
    Decidable (G.Fence who) := by
  unfold Fence
  infer_instance

/-- Under a fence, two independent nodes are never both readable by `who`. -/
theorem not_both_readable_of_independent {G : Graph Player L} {who : Player}
    {m n : Fin G.nodeCount}
    (hfence : G.Fence who) (hindep : G.Independent m n) (hmn : m ≠ n) :
    ¬ (G.NodeOutputReadableBy who m ∧ G.NodeOutputReadableBy who n) := by
  rintro ⟨hrm, hrn⟩
  exact hindep (hfence hrm hrn hmn)

/-- **Independent reorders preserve the readable-output order under a fence.**
Transposing two adjacent independent nodes leaves `who`'s readable-output order
unchanged: a fence forbids two independent nodes from both being readable, so the
only reorderings a linearization permits touch at most one readable node. -/
theorem readableOrder_swap_independent {G : Graph Player L} (who : Player)
    {m n : Fin G.nodeCount} (rest : List (Fin G.nodeCount))
    (hfence : G.Fence who) (hindep : G.Independent m n) (hmn : m ≠ n) :
    G.readableOrder who (m :: n :: rest) =
      G.readableOrder who (n :: m :: rest) :=
  readableOrder_swap_of_not_both G who rest
    (not_both_readable_of_independent hfence hindep hmn)

/-! ## Global invariance of the readable-output order -/

/-- A *linearization*: a dependency-respecting full order, in which no node
appears before something that is required before it. -/
def IsTopo (G : Graph Player L) (order : List (Fin G.nodeCount)) : Prop :=
  order.Nodup ∧ (∀ node : Fin G.nodeCount, node ∈ order) ∧
    order.Pairwise fun a b => ¬ G.Depends b a

/-- The canonical node order is always a linearization: dependencies point to
strictly earlier node ids (`prereq_lt`/`Depends.val_lt`), so the id order
respects them. -/
theorem nodeOrder_isTopo (G : Graph Player L) : G.IsTopo G.nodeOrder := by
  refine ⟨List.nodup_finRange _, mem_nodeOrder G, ?_⟩
  have hlt : G.nodeOrder.Pairwise (· < ·) := by
    unfold Graph.nodeOrder
    exact List.pairwise_lt_finRange _
  exact hlt.imp fun {a b} hab hdep =>
    absurd (Fin.lt_def.mpr hdep.val_lt) (lt_asymm hab)

/-- Under a fence, a player's readable-output projection of any linearization is
sorted by node id: the dependency relation orders all readable nodes, and a
dependency increases the id. -/
theorem readableOrder_sorted_of_fence {G : Graph Player L} {who : Player}
    {order : List (Fin G.nodeCount)}
    (htopo : G.IsTopo order) (hfence : G.Fence who) :
    (G.readableOrder who order).Pairwise (· < ·) := by
  have hcond :
      order.Pairwise fun a b =>
        G.NodeOutputReadableBy who a → G.NodeOutputReadableBy who b → a < b := by
    refine (htopo.2.2.and htopo.1).imp ?_
    rintro a b ⟨hndep, hne⟩ hra hrb
    rcases hfence hra hrb hne with hdab | hdba
    · exact Fin.lt_def.mpr hdab.val_lt
    · exact absurd hdba hndep
  have hsub :
      (G.readableOrder who order).Pairwise fun a b =>
        G.NodeOutputReadableBy who a → G.NodeOutputReadableBy who b → a < b :=
    List.Pairwise.sublist List.filter_sublist hcond
  exact hsub.imp_of_mem fun {a b} ha hb hr =>
    hr (by simpa using List.of_mem_filter ha) (by simpa using List.of_mem_filter hb)

/-- **Schedule invariance of the readable-output order.** Under a readability
fence, every linearization presents `who` the same readable-output order: the
order in which `who`'s readable values appear does not depend on the schedule.

This is *not* full schedule indistinguishability — occurrences are public, so the
order of all events is observable and schedule-dependent. It is exactly the
invariance of the values `who` can read.

It is the **strong-linearizability** content for `who`: under a fence, the
schedule (chosen adversarially) cannot reorder the readable values `who`
observes. It also discharges the schedule-invariance of the `Core_i` component in
the `Info ≅ Core × SchedulePrefix` factoring (the developer-facing reasoning
principle). -/
theorem readableOrder_eq_of_fence {G : Graph Player L} {who : Player}
    {o₁ o₂ : List (Fin G.nodeCount)}
    (h₁ : G.IsTopo o₁) (h₂ : G.IsTopo o₂) (hfence : G.Fence who) :
    G.readableOrder who o₁ = G.readableOrder who o₂ := by
  have : Std.Irrefl (α := Fin G.nodeCount) (· < ·) := ⟨fun a => lt_irrefl a⟩
  refine List.Pairwise.eq_of_mem_iff
    (readableOrder_sorted_of_fence h₁ hfence)
    (readableOrder_sorted_of_fence h₂ hfence) fun a => ?_
  simp only [readableOrder, List.mem_filter, h₁.2.1 a, h₂.2.1 a, true_and]

end Graph

end EventGraph

end Vegas
