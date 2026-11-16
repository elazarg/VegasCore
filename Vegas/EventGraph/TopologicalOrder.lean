module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Order
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

/-! # Topological event orders and adjacent swaps

The event-order skeleton is independent of node code, values and player policies.
A topological order lists every event once and places every direct predecessor
before its event. Adjacent events can exchange positions when neither is a
direct predecessor of the other.
-/

namespace Vegas.EventOrder

/-- A complete enumeration respecting every direct dependency. -/
structure Topological (order : EventOrder) (events : List (Fin order.eventCount)) : Prop where
  permutation : events.Perm (List.finRange order.eventCount)
  predecessor_before : ∀ predecessor event, predecessor ∈ order.predecessors event →
    events.idxOf predecessor < events.idxOf event

namespace Topological

variable {order : EventOrder} {events : List (Fin order.eventCount)}

theorem nodup (topological : order.Topological events) : events.Nodup :=
  topological.permutation.nodup_iff.mpr (List.nodup_finRange _)

theorem mem (topological : order.Topological events) (event : Fin order.eventCount) :
    event ∈ events :=
  topological.permutation.mem_iff.mpr (List.mem_finRange event)

theorem length (topological : order.Topological events) : events.length = order.eventCount := by
  simpa using topological.permutation.length_eq

end Topological

/-- Numeric source rank is one topological order, including when there are no events. -/
theorem topological_finRange (order : EventOrder) :
    order.Topological (List.finRange order.eventCount) where
  permutation := .refl _
  predecessor_before predecessor event member := by
    simpa using order.predecessor_lt member

/-- Independence for event-order swaps: distinct events with no direct edge in either direction. -/
def EdgeIndependent (order : EventOrder) (left right : Fin order.eventCount) : Prop :=
  left ≠ right ∧ left ∉ order.predecessors right ∧ right ∉ order.predecessors left

/-- Exchange two adjacent independent events, leaving their prefix and suffix fixed. -/
def AdjacentSwap (order : EventOrder)
    (before after : List (Fin order.eventCount)) : Prop :=
  ∃ front left right rest, order.EdgeIndependent left right ∧
    before = front ++ left :: right :: rest ∧ after = front ++ right :: left :: rest

variable {order : EventOrder}

private def Compatible (events : List (Fin order.eventCount)) : Prop :=
  events.Pairwise fun first second => second ∉ order.predecessors first

private theorem Topological.compatible {events : List (Fin order.eventCount)}
    (topological : order.Topological events) : Compatible (order := order) events := by
  rw [Compatible, List.pairwise_iff_getElem]
  intro first second firstBound secondBound earlier edge
  have reversed := topological.predecessor_before _ _ edge
  rw [topological.nodup.idxOf_getElem second,
    topological.nodup.idxOf_getElem first] at reversed
  omega

private theorem topological_of_compatible {events : List (Fin order.eventCount)}
    (permutation : events.Perm (List.finRange order.eventCount))
    (compatible : Compatible (order := order) events) : order.Topological events := by
  refine ⟨permutation, ?_⟩
  intro predecessor event edge
  have predecessorMem : predecessor ∈ events := permutation.mem_iff.mpr (List.mem_finRange _)
  have eventMem : event ∈ events := permutation.mem_iff.mpr (List.mem_finRange _)
  have predecessorBound := List.idxOf_lt_length_of_mem predecessorMem
  have eventBound := List.idxOf_lt_length_of_mem eventMem
  rcases lt_trichotomy (events.idxOf predecessor) (events.idxOf event) with earlier | same | later
  · exact earlier
  · have equal : predecessor = event := by
      have := congrArg (fun index => events[index]?) same
      simpa only [List.getElem?_eq_getElem predecessorBound, List.getElem?_eq_getElem eventBound,
        List.getElem_idxOf, Option.some.injEq] using this
    subst event
    have := order.predecessor_lt edge
    omega
  · have forbidden := compatible.rel_getElem_of_lt eventBound predecessorBound later
    simp only [List.getElem_idxOf] at forbidden
    exact False.elim (forbidden edge)

private theorem adjacentSwap_perm {before after : List (Fin order.eventCount)}
    (swap : order.AdjacentSwap before after) : before.Perm after := by
  obtain ⟨front, left, right, rest, _, rfl, rfl⟩ := swap
  exact (List.Perm.swap right left rest).append_left front

private theorem adjacentSwap_compatible {before after : List (Fin order.eventCount)}
    (swap : order.AdjacentSwap before after)
    (compatible : Compatible (order := order) before) : Compatible (order := order) after := by
  obtain ⟨front, left, right, rest, independent, rfl, rfl⟩ := swap
  simp only [Compatible, List.pairwise_append, List.pairwise_cons, List.mem_cons,
    forall_eq_or_imp] at compatible ⊢
  exact ⟨compatible.1, ⟨⟨independent.2.1, compatible.2.1.2.1⟩,
    compatible.2.1.1.2, compatible.2.1.2.2⟩,
    fun event member => ⟨(compatible.2.2 event member).2.1,
      (compatible.2.2 event member).1, (compatible.2.2 event member).2.2⟩⟩

private theorem adjacentSwap_cons (head : Fin order.eventCount)
    {before after : List (Fin order.eventCount)} (swap : order.AdjacentSwap before after) :
    order.AdjacentSwap (head :: before) (head :: after) := by
  obtain ⟨front, left, right, rest, independent, rfl, rfl⟩ := swap
  exact ⟨head :: front, left, right, rest, independent, rfl, rfl⟩

private theorem swaps_cons (head : Fin order.eventCount)
    {before after : List (Fin order.eventCount)}
    (swaps : Relation.ReflTransGen order.AdjacentSwap before after) :
    Relation.ReflTransGen order.AdjacentSwap (head :: before) (head :: after) := by
  induction swaps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (adjacentSwap_cons head step)

private theorem moveToFront (front rest : List (Fin order.eventCount))
    (event : Fin order.eventCount)
    (independent : ∀ prior ∈ front, order.EdgeIndependent prior event) :
    Relation.ReflTransGen order.AdjacentSwap (front ++ event :: rest)
      (event :: (front ++ rest)) := by
  induction front with
  | nil => exact .refl
  | cons head front ih =>
      have moved := swaps_cons head (ih fun prior member =>
        independent prior (List.mem_cons_of_mem head member))
      exact moved.tail ⟨[], head, event, front ++ rest,
        independent head (List.mem_cons_self), rfl, rfl⟩

private theorem compatible_connects {before after : List (Fin order.eventCount)}
    (permutation : before.Perm after) (nodup : before.Nodup)
    (beforeCompatible : Compatible (order := order) before)
    (afterCompatible : Compatible (order := order) after) :
    Relation.ReflTransGen order.AdjacentSwap before after := by
  induction after generalizing before with
  | nil =>
      have := permutation.eq_nil
      subst before
      exact .refl
  | cons event after ih =>
      have member : event ∈ before := permutation.mem_iff.mpr (List.mem_cons_self)
      obtain ⟨front, rest, rfl⟩ := List.mem_iff_append.mp member
      have reducedPerm : (front ++ rest).Perm after := by
        have movedPerm : (event :: (front ++ rest)).Perm (front ++ event :: rest) :=
          (List.perm_middle).symm
        exact List.Perm.cons_inv (movedPerm.trans permutation)
      have reducedNodup : (front ++ rest).Nodup := by
        have := (List.perm_middle : (front ++ event :: rest).Perm
          (event :: (front ++ rest))).nodup_iff.mp nodup
        exact this.of_cons
      have reducedCompatible : Compatible (order := order) (front ++ rest) := by
        simp only [Compatible, List.pairwise_append, List.pairwise_cons] at beforeCompatible ⊢
        exact ⟨beforeCompatible.1, beforeCompatible.2.1.2,
          fun first firstMem second secondMem =>
            beforeCompatible.2.2 first firstMem second (List.mem_cons_of_mem event secondMem)⟩
      have moved := moveToFront front rest event (by
        intro prior priorMem
        have different : prior ≠ event := by
          have noEvent : event ∉ front := by
            have := (List.perm_middle : (front ++ event :: rest).Perm
              (event :: (front ++ rest))).nodup_iff.mp nodup
            exact fun member => (List.nodup_cons.mp this).1 (List.mem_append_left rest member)
          exact fun same => noEvent (same ▸ priorMem)
        have first : prior ∉ order.predecessors event := by
          have priorAfter : prior ∈ after := by
            have := reducedPerm.mem_iff.mp (List.mem_append_left rest priorMem)
            exact this
          exact (List.pairwise_cons.mp afterCompatible).1 prior priorAfter
        have second : event ∉ order.predecessors prior :=
          (List.pairwise_append.mp beforeCompatible).2.2 prior priorMem event (List.mem_cons_self)
        exact ⟨different, first, second⟩)
      exact moved.trans (swaps_cons event (ih reducedPerm reducedNodup reducedCompatible
        (List.pairwise_cons.mp afterCompatible).2))

/-- Every two topological orders are connected by adjacent independent swaps. -/
theorem Topological.connects {before after : List (Fin order.eventCount)}
    (beforeTopological : order.Topological before) (afterTopological : order.Topological after) :
    Relation.ReflTransGen order.AdjacentSwap before after :=
  compatible_connects (beforeTopological.permutation.trans afterTopological.permutation.symm)
    beforeTopological.nodup beforeTopological.compatible afterTopological.compatible

/-- Topological orders are exactly the adjacent-swap component of source rank. -/
theorem topological_iff_swaps (events : List (Fin order.eventCount)) :
    order.Topological events ↔
      Relation.ReflTransGen order.AdjacentSwap (List.finRange order.eventCount) events := by
  constructor
  · exact (topological_finRange order).connects
  · intro swaps
    induction swaps with
    | refl => exact topological_finRange order
    | tail _ step ih =>
        exact topological_of_compatible
          ((adjacentSwap_perm step).symm.trans ih.permutation)
          (adjacentSwap_compatible step ih.compatible)

end Vegas.EventOrder
