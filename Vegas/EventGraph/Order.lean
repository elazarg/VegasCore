/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Find

/-! # Finite event orders and completed cuts

This module contains the source- and runtime-independent dependency carrier for
event graphs. Event identifiers are numbered in one fixed topological rank,
but readiness permits every event whose direct predecessors are complete; the
rank does not select the next event to execute.
-/

namespace Vegas

/-- A finite event set with direct predecessors oriented by a fixed
topological rank. -/
structure EventOrder where
  eventCount : Nat
  predecessors : Fin eventCount → Finset (Fin eventCount)
  predecessor_lt : ∀ {event predecessor},
    predecessor ∈ predecessors event → predecessor.val < event.val

namespace EventOrder

/-- A predecessor-closed set of completed events. -/
structure Cut (order : EventOrder) where
  completed : Finset (Fin order.eventCount)
  predecessor_closed : ∀ {event}, event ∈ completed →
    order.predecessors event ⊆ completed

namespace Cut

variable {order : EventOrder}

@[ext] theorem ext {left right : Cut order}
    (completed : left.completed = right.completed) : left = right := by
  cases left
  cases right
  cases completed
  rfl

/-- The initial cut has no completed events. -/
def empty (order : EventOrder) : Cut order where
  completed := ∅
  predecessor_closed := by simp

/-- An event is ready when it is unfinished and all its direct predecessors
are complete. -/
def Ready (cut : Cut order) (event : Fin order.eventCount) : Prop :=
  event ∉ cut.completed ∧ order.predecessors event ⊆ cut.completed

instance (cut : Cut order) (event : Fin order.eventCount) :
    Decidable (cut.Ready event) := by
  unfold Ready
  infer_instance

/-- The executable finite set of all currently ready events. -/
def enabled (cut : Cut order) : Finset (Fin order.eventCount) :=
  Finset.univ.filter cut.Ready

@[simp] theorem mem_enabled (cut : Cut order) (event : Fin order.eventCount) :
    event ∈ cut.enabled ↔ cut.Ready event := by
  simp [enabled]

/-- A cut is terminal when every event is complete. -/
def Terminal (cut : Cut order) : Prop :=
  cut.completed = Finset.univ

/-- Complete one ready event. -/
def complete (cut : Cut order) (event : Fin order.eventCount)
    (ready : cut.Ready event) : Cut order where
  completed := insert event cut.completed
  predecessor_closed := by
    intro completedEvent completedEventMem
    rw [Finset.mem_insert] at completedEventMem
    rcases completedEventMem with rfl | completedEventMem
    · exact ready.2.trans (Finset.subset_insert _ _)
    · exact (cut.predecessor_closed completedEventMem).trans
        (Finset.subset_insert event cut.completed)

@[simp] theorem completed_complete (cut : Cut order)
    (event : Fin order.eventCount) (ready : cut.Ready event) :
    (cut.complete event ready).completed = insert event cut.completed := rfl

@[simp] theorem mem_complete (cut : Cut order)
    (event : Fin order.eventCount) (ready : cut.Ready event)
    (query : Fin order.eventCount) :
    query ∈ (cut.complete event ready).completed ↔
      query = event ∨ query ∈ cut.completed := by
  simp [complete]

/-- Completion only enlarges the completed set. -/
theorem completed_subset_complete (cut : Cut order)
    (event : Fin order.eventCount) (ready : cut.Ready event) :
    cut.completed ⊆ (cut.complete event ready).completed := by
  exact Finset.subset_insert event cut.completed

/-- Completing a ready event increases the number of completed events by one. -/
@[simp] theorem card_complete (cut : Cut order)
    (event : Fin order.eventCount) (ready : cut.Ready event) :
    (cut.complete event ready).completed.card = cut.completed.card + 1 := by
  simp [complete, ready.1]

/-- A distinct ready event remains ready after another ready event completes. -/
theorem Ready.after_complete {cut : Cut order}
    {event other : Fin order.eventCount}
    (otherReady : cut.Ready other) (eventReady : cut.Ready event)
    (different : other ≠ event) :
    (cut.complete event eventReady).Ready other := by
  constructor
  · simp [complete, different, otherReady.1]
  · exact otherReady.2.trans (Finset.subset_insert event cut.completed)

/-- Completing two distinct ready events commutes. -/
theorem complete_comm {cut : Cut order} {left right : Fin order.eventCount}
    (leftReady : cut.Ready left) (rightReady : cut.Ready right)
    (different : left ≠ right) :
    (cut.complete left leftReady).complete right
        (rightReady.after_complete leftReady different.symm) =
      (cut.complete right rightReady).complete left
        (leftReady.after_complete rightReady different) := by
  apply Cut.ext
  simp only [completed_complete]
  exact Finset.insert_comm right left cut.completed

/-- Every unfinished event has some ready event no later in the fixed numeric
topological rank. -/
theorem exists_ready_le_of_unfinished (cut : Cut order)
    (event : Fin order.eventCount) (unfinished : event ∉ cut.completed) :
    ∃ readyEvent : Fin order.eventCount,
      cut.Ready readyEvent ∧ readyEvent.val ≤ event.val := by
  have missingNat : ∃ value : Nat, ∃ inRange : value < order.eventCount,
      (⟨value, inRange⟩ : Fin order.eventCount) ∉ cut.completed :=
    ⟨event.val, event.isLt, unfinished⟩
  obtain ⟨readyInRange, readyUnfinished⟩ := Nat.find_spec missingNat
  let readyEvent : Fin order.eventCount := ⟨Nat.find missingNat, readyInRange⟩
  have readyLe : readyEvent.val ≤ event.val :=
    Nat.find_min' missingNat ⟨event.isLt, unfinished⟩
  refine ⟨readyEvent, ⟨readyUnfinished, ?_⟩, readyLe⟩
  intro predecessor predecessorMem
  by_contra predecessorUnfinished
  have predecessorCandidate :
      ∃ inRange : predecessor.val < order.eventCount,
        (⟨predecessor.val, inRange⟩ : Fin order.eventCount) ∉ cut.completed :=
    ⟨predecessor.isLt, by simpa using predecessorUnfinished⟩
  exact (Nat.find_min missingNat (order.predecessor_lt predecessorMem))
    predecessorCandidate

/-- A nonterminal predecessor-closed cut has a ready event. -/
theorem exists_ready_of_not_terminal (cut : Cut order)
    (notTerminal : ¬ cut.Terminal) :
    ∃ event : Fin order.eventCount, cut.Ready event := by
  have missing : ∃ event : Fin order.eventCount, event ∉ cut.completed := by
    by_contra noneMissing
    apply notTerminal
    unfold Terminal
    apply Finset.eq_univ_of_forall
    intro event
    by_contra eventMissing
    exact noneMissing ⟨event, eventMissing⟩
  obtain ⟨event, eventMissing⟩ := missing
  obtain ⟨readyEvent, ready, _⟩ := cut.exists_ready_le_of_unfinished event eventMissing
  exact ⟨readyEvent, ready⟩

end Cut

end EventOrder

end Vegas
