module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Dependencies
public import Vegas.EventGraph.BarrierInformation

@[expose] public section

/-! # Source-rank dependency specialization

Adding every source-earlier event as a predecessor preserves the complete
chronological source prefix, including public default metadata. This is an
explicit information-order policy on the same typed event graph.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

/-- The complete source-rank dependency relation. -/
def sequentialDependencies (graph : Vegas.EventGraph Player L) : graph.Dependencies where
  predecessors := (EventOrder.sequential graph.order.eventCount).predecessors
  predecessor_lt := fun member =>
    (EventOrder.sequential.mem_predecessors _ _).mp member
  reads_available := by
    intro event producer read
    apply (EventOrder.sequential.mem_predecessors producer event).mpr
    exact graph.order.predecessor_lt
      (graph.reads_available event (.inr producer)
        ((graph.mem_readPredecessors producer event).mp read))

/-- Every admissible dependency choice is contained in the source-rank order. -/
theorem dependencies_predecessors_subset_sequential (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) (event : graph.EventId) :
    dependencies.predecessors event ⊆ graph.sequentialDependencies.predecessors event := by
  intro producer member
  exact (EventOrder.sequential.mem_predecessors producer event).mpr
    (dependencies.predecessor_lt member)

/-- Apply the complete source-rank information-order policy without changing
typed fields, event code or payoffs. -/
abbrev sequentialize (graph : Vegas.EventGraph Player L) : Vegas.EventGraph Player L :=
  graph.withDependencies graph.sequentialDependencies

@[simp] theorem sequentialize_inputCount (graph : Vegas.EventGraph Player L) :
    graph.sequentialize.inputCount = graph.inputCount := rfl

@[simp] theorem sequentialize_eventCount (graph : Vegas.EventGraph Player L) :
    graph.sequentialize.order.eventCount = graph.order.eventCount := rfl

@[simp] theorem sequentialize_predecessors (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.sequentialize.order.predecessors event =
      Finset.univ.filter fun prior => prior.val < event.val := rfl

@[simp] theorem sequentialize_inputLayout (graph : Vegas.EventGraph Player L)
    (input : graph.InputId) :
    graph.sequentialize.inputLayout input = graph.inputLayout input := rfl

@[simp] theorem sequentialize_outputLayout (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.sequentialize.outputLayout event = graph.outputLayout event := rfl

@[simp] theorem sequentialize_nodes (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.sequentialize.nodes event = graph.nodes event := rfl

@[simp] theorem sequentialize_payoffs (graph : Vegas.EventGraph Player L) :
    graph.sequentialize.payoffs = graph.payoffs := rfl

@[simp] theorem sequentialize_idem (graph : Vegas.EventGraph Player L) :
    graph.sequentialize.sequentialize = graph.sequentialize := by
  cases graph
  rfl

/-- Choosing the source-rank policy replaces any previous dependency choice. -/
@[simp] theorem withDependencies_sequentialize (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    (graph.withDependencies dependencies).sequentialize = graph.sequentialize := by
  cases graph
  rfl

variable [DecidableEq Player]

/-- The source-rank policy contains all public barriers and same-owner
dependencies. -/
theorem sequentialize_barrierOrdered (graph : Vegas.EventGraph Player L) :
    graph.sequentialize.BarrierOrdered := by
  intro event producer member
  exact (EventOrder.sequential.mem_predecessors producer event).mpr
    ((mem_barrierOrder graph.outputLayout producer event).mp member).1

omit [DecidableEq Player] in
/-- The sequential specialization admits at most one ready event. -/
theorem sequentialize_ready_unique (graph : Vegas.EventGraph Player L)
    (cut : graph.sequentialize.order.Cut) {left right : graph.EventId}
    (leftReady : cut.Ready left) (rightReady : cut.Ready right) : left = right :=
  cut.ready_unique leftReady rightReady

omit [DecidableEq Player] in
/-- A ready sequential event is the least unfinished source-ranked event. -/
theorem sequentialize_ready_le_unfinished (graph : Vegas.EventGraph Player L)
    (cut : graph.sequentialize.order.Cut) {event other : graph.EventId}
    (ready : cut.Ready event) (unfinished : other ∉ cut.completed) :
    event.val ≤ other.val :=
  cut.ready_le_unfinished ready unfinished

omit [DecidableEq Player] in
/-- The completed cut before a ready sequential event is exactly its strict
source-ranked prefix. -/
theorem sequentialize_mem_completed_iff_lt_of_ready
    (graph : Vegas.EventGraph Player L) (cut : graph.sequentialize.order.Cut)
    {event other : graph.EventId} (ready : cut.Ready event) :
    other ∈ cut.completed ↔ other.val < event.val :=
  cut.mem_completed_iff_lt_of_ready ready

end Vegas.EventGraph
