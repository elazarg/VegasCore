/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.RevealRelaxation

/-! # Sequential dependency specialization

The sequential specialization retains an event graph's fields, code, and
source ranking while adding every earlier event as a direct predecessor.
Consequently the ordinary ready-event executor and pending-message runtime can
only complete the least unfinished event.  This is a dependency constraint on
the shared graph, not a second execution model or a service-order convention.
-/

noncomputable section

namespace Vegas


namespace EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]

/-- Dependency constraint used by an EventGraph execution: the graph's own
dependencies, the total source ranking, or the graph's dependencies without the
direct ones between independent reveals. -/
inductive ExecutionMode where
  | concurrent
  | sequential
  | concurrentReveals
  deriving DecidableEq, Repr

/-- The graph's dependencies of an event, without those on reveals it is
independent of. -/
def revealRelaxedPredecessors (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) : Finset graph.EventId := by
  classical
  exact (graph.order.predecessors event).filter fun prior =>
    ¬ graph.IndependentReveals prior event

omit [DecidableEq Player] in
theorem mem_revealRelaxedPredecessors (graph : Vegas.EventGraph Player L)
    (prior event : graph.EventId) :
    prior ∈ graph.revealRelaxedPredecessors event ↔
      prior ∈ graph.order.predecessors event ∧ ¬ graph.IndependentReveals prior event := by
  classical
  simp [revealRelaxedPredecessors]

/-- Apply an execution mode by changing only the graph's dependency order. -/
def withMode (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) : Vegas.EventGraph Player L where
  inputCount := graph.inputCount
  order := {
    eventCount := graph.order.eventCount
    predecessors := fun event => match mode with
      | .concurrent => graph.order.predecessors event
      | .sequential => (EventOrder.sequential graph.order.eventCount).predecessors event
      | .concurrentReveals => graph.revealRelaxedPredecessors event
    predecessor_lt := by
      intro event predecessor member
      cases mode with
      | concurrent => exact graph.order.predecessor_lt member
      | sequential => exact (EventOrder.sequential.mem_predecessors predecessor event).1 member
      | concurrentReveals =>
          exact graph.order.predecessor_lt
            ((graph.mem_revealRelaxedPredecessors predecessor event).1 member).1 }
  inputLayout := graph.inputLayout
  outputLayout := graph.outputLayout
  nodes := graph.nodes
  reads_available := by
    intro event field read
    cases mode with
    | concurrent => exact graph.reads_available event field read
    | sequential =>
        cases field with
        | inl => trivial
        | inr producer =>
            apply (EventOrder.sequential.mem_predecessors producer event).2
            exact graph.order.predecessor_lt
              (graph.reads_available event (.inr producer) read)
    | concurrentReveals =>
        cases field with
        | inl => trivial
        | inr producer =>
            exact (graph.mem_revealRelaxedPredecessors producer event).2
              ⟨graph.reads_available event (.inr producer) read,
                fun independent => independent.2.2.1 read⟩
  payoffs := graph.payoffs

omit [DecidableEq Player] in
@[simp] theorem withMode_concurrent (graph : Vegas.EventGraph Player L) :
    graph.withMode .concurrent = graph := by
  cases graph
  rfl

/-- Add all source-earlier dependencies to an event graph while retaining its
typed fields, event code, and terminal payoff expressions: the sequential
dependency mode. -/
abbrev sequentialize (graph : Vegas.EventGraph Player L) : Vegas.EventGraph Player L :=
  graph.withMode .sequential

omit [DecidableEq Player] in
@[simp] theorem withMode_inputCount (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) :
    (graph.withMode mode).inputCount = graph.inputCount := rfl

omit [DecidableEq Player] in
@[simp] theorem withMode_eventCount (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) :
    (graph.withMode mode).order.eventCount = graph.order.eventCount := rfl

omit [DecidableEq Player] in
@[simp] theorem withMode_inputLayout (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) (input : graph.InputId) :
    (graph.withMode mode).inputLayout input = graph.inputLayout input := rfl

omit [DecidableEq Player] in
@[simp] theorem withMode_outputLayout (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) (event : graph.EventId) :
    (graph.withMode mode).outputLayout event = graph.outputLayout event := rfl

omit [DecidableEq Player] in
@[simp] theorem withMode_nodes (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) (event : graph.EventId) :
    (graph.withMode mode).nodes event = graph.nodes event := rfl

omit [DecidableEq Player] in
@[simp] theorem withMode_payoffs (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) :
    (graph.withMode mode).payoffs = graph.payoffs := rfl

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

/-- Required public barriers survive every dependency mode that keeps the
dependencies between reveals. -/
theorem withMode_barrierOrdered (graph : Vegas.EventGraph Player L)
    (ordered : graph.BarrierOrdered) (mode : ExecutionMode)
    (keepsReveals : mode ≠ .concurrentReveals) :
    (graph.withMode mode).BarrierOrdered := by
  cases mode with
  | concurrent => exact ordered
  | sequential => exact graph.sequentialize_barrierOrdered
  | concurrentReveals => exact absurd rfl keepsReveals

omit [DecidableEq Player] in
@[simp] theorem withMode_concurrentReveals_predecessors (graph : Vegas.EventGraph Player L)
    (prior event : graph.EventId) :
    prior ∈ (graph.withMode .concurrentReveals).order.predecessors event ↔
      prior ∈ graph.order.predecessors event ∧ ¬ graph.IndependentReveals prior event :=
  graph.mem_revealRelaxedPredecessors prior event

/-- Every dependency mode keeps the public-barrier dependencies except possibly
those between independent reveals. -/
theorem withMode_revealRelaxedOrdered (graph : Vegas.EventGraph Player L)
    (ordered : graph.BarrierOrdered) (mode : ExecutionMode) :
    (graph.withMode mode).RevealRelaxedOrdered := by
  cases mode with
  | concurrentReveals =>
      intro event prior member dependent
      exact (graph.mem_revealRelaxedPredecessors prior event).2
        ⟨ordered event member, dependent⟩
  | concurrent | sequential =>
      exact BarrierOrdered.revealRelaxedOrdered
        (graph.withMode_barrierOrdered ordered _ (by simp))

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
