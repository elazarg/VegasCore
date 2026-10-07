/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.RevealRelaxation
import Vegas.EventGraph.CanonicalStep

/-! # Runs of independent bindings between public barriers

Under the barrier order, a maximal run of binding events between two public
events forms a block: once the events before the block have completed, only
block events can become ready until the whole block has completed, whatever
order they complete in. A cut whose completed events contain every event below
the block and none at or beyond its end stays so when a ready event completes
(`Vegas.EventOrder.Cut.Within.complete`), and its ready events lie in the block
until the block is complete (`Vegas.EventGraph.BarrierOrdered.ready_lt_of_within`).
-/

namespace Vegas.EventOrder.Cut

variable {order : EventOrder}

/-- Every event below `low` has completed and no event at or beyond `high` has. -/
def Within (cut : order.Cut) (low high : Nat) : Prop :=
  (∀ event : Fin order.eventCount, event.val < low → event ∈ cut.completed) ∧
    ∀ event ∈ cut.completed, event.val < high

/-- A completed prefix lies within itself and every later end. -/
theorem IsPrefix.within {cut : order.Cut} {low high : Nat} (ordered : cut.IsPrefix low)
    (later : low ≤ high) : cut.Within low high :=
  ⟨fun event below => (ordered.2 event).mpr below,
    fun event member => Nat.lt_of_lt_of_le ((ordered.2 event).mp member) later⟩

/-- A cut within a block whose events have all completed is the prefix up to
the block's end. -/
theorem Within.isPrefix {cut : order.Cut} {low high : Nat} (within : cut.Within low high)
    (bounded : high ≤ order.eventCount)
    (complete : ∀ event : Fin order.eventCount, event.val < high → event ∈ cut.completed) :
    cut.IsPrefix high :=
  ⟨bounded, fun event => ⟨within.2 event, complete event⟩⟩

/-- Completing a ready event below the block's end keeps the cut within the
block. -/
theorem Within.complete {cut : order.Cut} {low high : Nat} (within : cut.Within low high)
    (event : Fin order.eventCount) (ready : cut.Ready event) (below : event.val < high) :
    (cut.complete event ready).Within low high := by
  refine ⟨fun other lower => (mem_complete cut event ready other).mpr
    (Or.inr (within.1 other lower)), fun other member => ?_⟩
  rcases (mem_complete cut event ready other).mp member with same | old
  · rw [same]
    exact below
  · exact within.2 other old

/-- A cut within a block is within every later end. -/
theorem Within.mono_high {cut : order.Cut} {low high high' : Nat}
    (within : cut.Within low high) (larger : high ≤ high') : cut.Within low high' :=
  ⟨within.1, fun event member => Nat.lt_of_lt_of_le (within.2 event member) larger⟩

end Vegas.EventOrder.Cut

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- **Ready events stay in the block.** On a barrier-ordered graph, at a cut
within a block whose end is a public event or the end of the graph, every ready
event lies in the block unless every block event has completed. -/
theorem BarrierOrdered.ready_lt_of_within (ordered : graph.BarrierOrdered)
    {cut : graph.order.Cut} {low high : Nat} (within : cut.Within low high)
    (barrier : ∀ event : graph.EventId, event.val = high →
      (graph.outputLayout event).IsPublic)
    {event : graph.EventId} (ready : cut.Ready event) :
    event.val < high ∨ ∀ other : graph.EventId, other.val < high → other ∈ cut.completed := by
  by_cases inside : event.val < high
  · exact Or.inl inside
  · right
    intro other below
    by_contra missing
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt inside) with atEnd | beyond
    · have isPublic := barrier event atEnd.symm
      exact missing (ready.2 (ordered event (barrierOrder_public_event graph.outputLayout
        (by omega) isPublic)))
    · let wall : graph.EventId := ⟨high, Nat.lt_trans beyond event.isLt⟩
      have isPublic := barrier wall rfl
      have done := ready.2 (ordered event (barrierOrder_public_prior graph.outputLayout
        (show wall.val < event.val from beyond) isPublic))
      exact Nat.lt_irrefl _ (within.2 wall done)


/-- A reveal-relaxed graph keeps every barrier dependency of which one end is not
a publication. -/
theorem RevealRelaxedOrdered.keeps (relaxed : graph.RevealRelaxedOrdered)
    {prior event : graph.EventId}
    (member : prior ∈ (barrierOrder graph.outputLayout).predecessors event)
    (plain : ¬ (graph.outputLayout prior).IsPublication ∨
      ¬ (graph.outputLayout event).IsPublication) :
    prior ∈ graph.order.predecessors event :=
  relaxed event prior member fun independent =>
    plain.elim (fun notPrior => notPrior independent.1) (fun notEvent => notEvent independent.2.1)

/-- **Ready events stay in a block of non-publications.** On a reveal-relaxed
graph, at a cut within a block of events that are not publications, whose end
is a public event or the end of the graph, every ready event lies in the block
unless every block event has completed. -/
theorem RevealRelaxedOrdered.ready_lt_of_within (relaxed : graph.RevealRelaxedOrdered)
    {cut : graph.order.Cut} {low high : Nat} (within : cut.Within low high)
    (barrier : ∀ event : graph.EventId, event.val = high →
      (graph.outputLayout event).IsPublic)
    (plain : ∀ event : graph.EventId, low ≤ event.val → event.val < high →
      ¬ (graph.outputLayout event).IsPublication)
    {event : graph.EventId} (ready : cut.Ready event) :
    event.val < high ∨ ∀ other : graph.EventId, other.val < high → other ∈ cut.completed := by
  by_cases inside : event.val < high
  · exact Or.inl inside
  · right
    intro other below
    by_contra missing
    have lower : low ≤ other.val :=
      Nat.le_of_not_gt fun under => missing (within.1 other under)
    have otherPlain := plain other lower below
    by_cases eventPublic : (graph.outputLayout event).IsPublic
    · exact missing (ready.2 (relaxed.keeps (barrierOrder_public_event graph.outputLayout
        (by omega) eventPublic) (Or.inl otherPlain)))
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt inside) with atEnd | beyond
      · exact eventPublic (barrier event atEnd.symm)
      · let wall : graph.EventId := ⟨high, Nat.lt_trans beyond event.isLt⟩
        have wallPublic := barrier wall rfl
        have done := ready.2 (relaxed.keeps (barrierOrder_public_prior graph.outputLayout
          (show wall.val < event.val from beyond) wallPublic)
          (Or.inr fun publication => eventPublic publication.isPublic))
        exact Nat.lt_irrefl _ (within.2 wall done)


/-- **Ready events stay in a block of reveals.** On a reveal-relaxed graph, at
a cut within a block of publications whose end is an event that is not a
publication or the end of the graph, every ready event lies in the block unless
every block event has completed: a later non-publication waits for every
earlier publication, and a later publication waits for the block's end. -/
theorem RevealRelaxedOrdered.ready_lt_of_within_publications
    (relaxed : graph.RevealRelaxedOrdered)
    {cut : graph.order.Cut} {low high : Nat} (within : cut.Within low high)
    (barrier : ∀ event : graph.EventId, event.val = high →
      ¬ (graph.outputLayout event).IsPublication)
    (publications : ∀ event : graph.EventId, low ≤ event.val → event.val < high →
      (graph.outputLayout event).IsPublication)
    {event : graph.EventId} (ready : cut.Ready event) :
    event.val < high ∨ ∀ other : graph.EventId, other.val < high → other ∈ cut.completed := by
  by_cases inside : event.val < high
  · exact Or.inl inside
  · right
    intro other below
    by_contra missing
    have lower : low ≤ other.val :=
      Nat.le_of_not_gt fun under => missing (within.1 other under)
    have otherPublic := (publications other lower below).isPublic
    by_cases eventPublication : (graph.outputLayout event).IsPublication
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt inside) with atEnd | beyond
      · exact barrier event atEnd.symm eventPublication
      · let wall : graph.EventId := ⟨high, Nat.lt_trans beyond event.isLt⟩
        have done := ready.2 (relaxed.keeps (barrierOrder_public_event graph.outputLayout
          (show wall.val < event.val from beyond) eventPublication.isPublic)
          (Or.inl (barrier wall rfl)))
        exact Nat.lt_irrefl _ (within.2 wall done)
    · exact missing (ready.2 (relaxed.keeps (barrierOrder_public_prior graph.outputLayout
        (by omega) otherPublic) (Or.inr eventPublication)))

end Vegas.EventGraph
