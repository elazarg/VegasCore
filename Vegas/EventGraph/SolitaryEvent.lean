module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.RevealRelaxedScheduling

@[expose] public section

/-! # Solitary and leading events

An event is solitary when no other event is ready together with it, and leading
when every unfinished event comes no earlier than it in source order whenever it
is ready. Every event of a sequential graph is both. On a graph where only
independent reveals are concurrent, every event that is not a publication is
solitary, and leading when the graph is obtained by relaxing reveals in a total order.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- No other event is ready together with `event`. -/
def Solitary (event : graph.EventId) : Prop :=
  ∀ (cut : graph.order.Cut) {other : graph.EventId}, cut.Ready other → cut.Ready event →
    other = event

omit [DecidableEq Player] in
/-- A globally solitary event is also solitary among its owner's events. -/
theorem Solitary.ownerSolitary {event : graph.EventId} (solitary : graph.Solitary event) :
    graph.OwnerSolitary event := by
  intro cut _ _ ready otherReady _ _
  exact solitary cut otherReady ready

variable (graph) in
/-- Whenever `event` is ready, every unfinished event comes no earlier in source
order. -/
def Leading (event : graph.EventId) : Prop :=
  ∀ (cut : graph.order.Cut) {other : graph.EventId}, cut.Ready event →
    other ∉ cut.completed → event.val ≤ other.val

omit [DecidableEq Player] in
/-- Every event of a sequential graph is solitary. -/
theorem sequentialize_solitary (graph : Vegas.EventGraph Player L) (event : graph.EventId) :
    graph.sequentialize.Solitary event :=
  fun cut _ otherReady ready => graph.sequentialize_ready_unique cut otherReady ready

omit [DecidableEq Player] in
/-- Every event of a sequential graph is leading. -/
theorem sequentialize_leading (graph : Vegas.EventGraph Player L) (event : graph.EventId) :
    graph.sequentialize.Leading event :=
  fun cut _ ready unfinished => graph.sequentialize_ready_le_unfinished cut ready unfinished

omit [DecidableEq Player] in
/-- When only independent reveals are concurrent, an event that is not a
publication is solitary. -/
theorem RevealsOnlyConcurrent.solitary (only : graph.RevealsOnlyConcurrent)
    {event : graph.EventId} (notPublication : ¬ (graph.outputLayout event).IsPublication) :
    graph.Solitary event := by
  intro cut other otherReady ready
  by_contra different
  rcases only cut otherReady ready different with independent | independent
  · exact notPublication independent.2.1
  · exact notPublication independent.1

omit [DecidableEq Player] in
/-- Relaxing the reveal dependencies of a totally ordered graph keeps every
event that is not a publication leading. -/
theorem relaxReveals_leading (graph : Vegas.EventGraph Player L)
    (total : ∀ prior event : graph.EventId, prior.val < event.val →
      prior ∈ graph.order.predecessors event)
    {event : graph.EventId} (notPublication : ¬ (graph.outputLayout event).IsPublication) :
    (graph.relaxReveals).Leading event := by
  intro cut other ready unfinished
  by_contra later
  apply unfinished
  exact ready.2 ((graph.relaxReveals_predecessors other event).mpr
    ⟨total other event (by omega), fun independent => notPublication independent.2.1⟩)

end Vegas.EventGraph
