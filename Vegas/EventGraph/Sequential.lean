/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.BarrierInformation

/-! # Sequential dependency specialization

The sequential specialization retains an event graph's fields, code, and
source ranking while adding every earlier event as a direct predecessor.
Consequently the ordinary ready-event executor and pending-message runtime can
only complete the least unfinished event.  This is a dependency constraint on
the shared graph, not a second execution model or a service-order convention.
-/

noncomputable section

namespace Vegas

/-- The total source-ranked dependency order on a fixed finite event set. -/
def EventOrder.sequential (eventCount : Nat) : EventOrder where
  eventCount := eventCount
  predecessors event := Finset.univ.filter fun prior => prior.val < event.val
  predecessor_lt := by
    intro event predecessor member
    exact (Finset.mem_filter.mp member).2

namespace EventOrder.sequential

@[simp] theorem mem_predecessors {eventCount : Nat}
    (prior event : Fin eventCount) :
    prior ∈ (EventOrder.sequential eventCount).predecessors event ↔
      prior.val < event.val := by
  change prior ∈ Finset.univ.filter (fun candidate => candidate.val < event.val) ↔
    prior.val < event.val
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ prior))

end EventOrder.sequential

namespace EventOrder.Cut

/-- In a total source-ranked dependency order, two ready events coincide. -/
theorem ready_unique {eventCount : Nat}
    (cut : (EventOrder.sequential eventCount).Cut)
    {left right : Fin eventCount} (leftReady : cut.Ready left)
    (rightReady : cut.Ready right) : left = right := by
  rcases lt_trichotomy left.val right.val with before | same | after
  · exact False.elim (leftReady.1
      (rightReady.2 ((EventOrder.sequential.mem_predecessors left right).2 before)))
  · exact Fin.ext same
  · exact False.elim (rightReady.1
      (leftReady.2 ((EventOrder.sequential.mem_predecessors right left).2 after)))

/-- A ready event in a total source-ranked dependency order is the least
unfinished event. -/
theorem ready_le_unfinished {eventCount : Nat}
    (cut : (EventOrder.sequential eventCount).Cut)
    {event other : Fin eventCount} (ready : cut.Ready event)
    (unfinished : other ∉ cut.completed) : event.val ≤ other.val := by
  by_contra later
  have before : other.val < event.val := Nat.lt_of_not_ge later
  exact unfinished
    (ready.2 ((EventOrder.sequential.mem_predecessors other event).2 before))

/-- A ready event has exactly the earlier source-ranked prefix completed. -/
theorem mem_completed_iff_lt_of_ready {eventCount : Nat}
    (cut : (EventOrder.sequential eventCount).Cut)
    {event other : Fin eventCount} (ready : cut.Ready event) :
    other ∈ cut.completed ↔ other.val < event.val := by
  constructor
  · intro completed
    by_contra notBefore
    have weak : event.val ≤ other.val := Nat.le_of_not_gt notBefore
    rcases Nat.eq_or_lt_of_le weak with same | after
    · exact ready.1 (Fin.ext same ▸ completed)
    · have predecessor : event ∈
          (EventOrder.sequential eventCount).predecessors other :=
        (EventOrder.sequential.mem_predecessors event other).2 after
      exact ready.1 (cut.predecessor_closed completed predecessor)
  · intro before
    exact ready.2 ((EventOrder.sequential.mem_predecessors other event).2 before)

end EventOrder.Cut

namespace EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]

/-- Add all source-earlier dependencies to an event graph while retaining its
typed fields, event code, and terminal payoff expressions. -/
def sequentialize (graph : Vegas.EventGraph Player L) : Vegas.EventGraph Player L where
  inputCount := graph.inputCount
  order := EventOrder.sequential graph.order.eventCount
  inputLayout := graph.inputLayout
  outputLayout := graph.outputLayout
  nodes := graph.nodes
  reads_available := by
    intro event field read
    cases field with
    | inl => trivial
    | inr producer =>
        apply (EventOrder.sequential.mem_predecessors producer event).2
        exact graph.order.predecessor_lt (graph.reads_available event (.inr producer) read)
  payoffs := graph.payoffs

omit [DecidableEq Player] in
@[simp] theorem sequentialize_inputCount (graph : Vegas.EventGraph Player L) :
    graph.sequentialize.inputCount = graph.inputCount := rfl

omit [DecidableEq Player] in
@[simp] theorem sequentialize_eventCount (graph : Vegas.EventGraph Player L) :
    graph.sequentialize.order.eventCount = graph.order.eventCount := rfl

omit [DecidableEq Player] in
@[simp] theorem sequentialize_predecessors (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.sequentialize.order.predecessors event =
      Finset.univ.filter fun prior => prior.val < event.val := rfl

omit [DecidableEq Player] in
@[simp] theorem sequentialize_inputLayout (graph : Vegas.EventGraph Player L)
    (input : graph.InputId) :
    graph.sequentialize.inputLayout input = graph.inputLayout input := rfl

omit [DecidableEq Player] in
@[simp] theorem sequentialize_outputLayout (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.sequentialize.outputLayout event = graph.outputLayout event := rfl

omit [DecidableEq Player] in
@[simp] theorem sequentialize_nodes (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.sequentialize.nodes event = graph.nodes event := rfl

/-- The sequential specialization contains every required public-barrier and
same-owner dependency, so it satisfies the common strategic certificate. -/
theorem sequentialize_barrierOrdered (graph : Vegas.EventGraph Player L) :
    graph.sequentialize.BarrierOrdered := by
  intro event predecessor member
  exact (EventOrder.sequential.mem_predecessors predecessor event).2
    ((mem_barrierOrder graph.outputLayout predecessor event).1 member).1

omit [DecidableEq Player] in
/-- The sequential specialization admits at most one ready event. -/
theorem sequentialize_ready_unique (graph : Vegas.EventGraph Player L)
    (cut : graph.sequentialize.order.Cut) {left right : graph.EventId}
    (leftReady : cut.Ready left) (rightReady : cut.Ready right) : left = right :=
  cut.ready_unique leftReady rightReady

omit [DecidableEq Player] in
/-- Every ready event in the sequential specialization is the least unfinished
source-ranked event. -/
theorem sequentialize_ready_le_unfinished (graph : Vegas.EventGraph Player L)
    (cut : graph.sequentialize.order.Cut) {event other : graph.EventId}
    (ready : cut.Ready event) (unfinished : other ∉ cut.completed) :
    event.val ≤ other.val :=
  cut.ready_le_unfinished ready unfinished

omit [DecidableEq Player] in
/-- The completed cut before a ready sequential event is precisely its strict
source-ranked prefix. -/
theorem sequentialize_mem_completed_iff_lt_of_ready
    (graph : Vegas.EventGraph Player L) (cut : graph.sequentialize.order.Cut)
    {event other : graph.EventId} (ready : cut.Ready event) :
    other ∈ cut.completed ↔ other.val < event.val :=
  cut.mem_completed_iff_lt_of_ready ready

end EventGraph

end Vegas
