module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Basic

@[expose] public section

/-! # Dependency choices for one fixed event graph

A dependency choice orders the same event identities and makes every declared output read
available. Replacing it retains the graph's layouts, event code and payoff expressions literally.
The dependency carrier is indexed only by event count and declared reads, so replacing an order
does not change the type of later dependency choices.
-/

namespace Vegas

/-- A topologically ranked predecessor family covering all required producer reads. -/
structure EventDependencies (eventCount : Nat)
    (readPredecessors : Fin eventCount → Finset (Fin eventCount)) where
  predecessors : Fin eventCount → Finset (Fin eventCount)
  predecessor_lt : ∀ {event predecessor},
    predecessor ∈ predecessors event → predecessor.val < event.val
  reads_available : ∀ event, readPredecessors event ⊆ predecessors event

@[ext] theorem EventDependencies.ext {eventCount : Nat}
    {readPredecessors : Fin eventCount → Finset (Fin eventCount)}
    {left right : EventDependencies eventCount readPredecessors}
    (predecessors : left.predecessors = right.predecessors) : left = right := by
  cases left
  cases right
  cases predecessors
  rfl

namespace EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

/-- Exactly the output producers named in an event's declared reads. Initial inputs require no
predecessor because they are present before any event completes. -/
def readPredecessors (graph : Vegas.EventGraph Player L) (event : graph.EventId) :
    Finset graph.EventId :=
  Finset.univ.filter fun prior => (.inr prior : graph.Field) ∈ (graph.nodes event).readFields

@[simp] theorem mem_readPredecessors (graph : Vegas.EventGraph Player L)
    (prior event : graph.EventId) :
    prior ∈ graph.readPredecessors event ↔
      (.inr prior : graph.Field) ∈ (graph.nodes event).readFields := by
  simp only [readPredecessors, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The graph's rank puts each declared output read before its consumer. -/
theorem readPredecessor_lt (graph : Vegas.EventGraph Player L) {event prior : graph.EventId}
    (read : prior ∈ graph.readPredecessors event) : prior.val < event.val :=
  graph.order.predecessor_lt
    (graph.reads_available event (.inr prior) ((graph.mem_readPredecessors prior event).mp read))

/-- Dependency choices for the immutable event identities and declared reads of a graph. -/
abbrev Dependencies (graph : Vegas.EventGraph Player L) :=
  EventDependencies graph.order.eventCount graph.readPredecessors

/-- The predecessor family already supplied by a graph. -/
def dependencies (graph : Vegas.EventGraph Player L) : graph.Dependencies where
  predecessors := graph.order.predecessors
  predecessor_lt := graph.order.predecessor_lt
  reads_available event prior read :=
    graph.reads_available event (.inr prior) ((graph.mem_readPredecessors prior event).mp read)

/-- Replace only dependencies; fields, node code, event identities and payoff expressions retain
their definitionally identical types. -/
def withDependencies (graph : Vegas.EventGraph Player L) (dependencies : graph.Dependencies) :
    Vegas.EventGraph Player L where
  inputCount := graph.inputCount
  order := {
    eventCount := graph.order.eventCount
    predecessors := dependencies.predecessors
    predecessor_lt := dependencies.predecessor_lt }
  inputLayout := graph.inputLayout
  outputLayout := graph.outputLayout
  nodes := graph.nodes
  reads_available := by
    intro event field read
    cases field with
    | inl input => trivial
    | inr prior =>
        exact dependencies.reads_available event
          ((graph.mem_readPredecessors prior event).mpr read)
  payoffs := graph.payoffs

@[simp] theorem withDependencies_inputCount (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    (graph.withDependencies dependencies).inputCount = graph.inputCount := rfl

@[simp] theorem withDependencies_eventCount (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    (graph.withDependencies dependencies).order.eventCount = graph.order.eventCount := rfl

@[simp] theorem withDependencies_predecessors (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) (event : graph.EventId) :
    (graph.withDependencies dependencies).order.predecessors event =
      dependencies.predecessors event := rfl

@[simp] theorem withDependencies_inputLayout (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) (input : graph.InputId) :
    (graph.withDependencies dependencies).inputLayout input = graph.inputLayout input := rfl

@[simp] theorem withDependencies_outputLayout (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) (event : graph.EventId) :
    (graph.withDependencies dependencies).outputLayout event = graph.outputLayout event := rfl

@[simp] theorem withDependencies_nodes (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) (event : graph.EventId) :
    (graph.withDependencies dependencies).nodes event = graph.nodes event := rfl

@[simp] theorem withDependencies_payoffs (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    (graph.withDependencies dependencies).payoffs = graph.payoffs := rfl

@[simp] theorem withDependencies_readPredecessors (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    (graph.withDependencies dependencies).readPredecessors = graph.readPredecessors := rfl

@[simp] theorem withDependencies_dependencies (graph : Vegas.EventGraph Player L) :
    graph.withDependencies graph.dependencies = graph := by
  cases graph
  rfl

@[simp] theorem dependencies_withDependencies (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    (graph.withDependencies dependencies).dependencies = dependencies := by
  cases dependencies
  rfl

/-- Later replacement uses the same dependency carrier and supersedes the earlier choice. -/
@[simp] theorem withDependencies_replace (graph : Vegas.EventGraph Player L)
    (first second : graph.Dependencies) :
    (graph.withDependencies first).withDependencies second = graph.withDependencies second := rfl

/-- An event depends on another through a chain of predecessor edges. -/
def DependsOn (graph : Vegas.EventGraph Player L) (prior later : graph.EventId) : Prop :=
  Relation.ReflTransGen (fun before after => before ∈ graph.order.predecessors after) prior later

/-- A completed event's dependencies have completed. -/
theorem DependsOn.completed {graph : Vegas.EventGraph Player L} {prior later : graph.EventId}
    (depends : graph.DependsOn prior later) {cut : graph.order.Cut}
    (done : later ∈ cut.completed) : prior ∈ cut.completed := by
  induction depends using Relation.ReflTransGen.head_induction_on with
  | refl => exact done
  | head member _ ih => exact cut.predecessor_closed ih member

/-- A dependency is no later than the event depending on it. -/
theorem DependsOn.le {graph : Vegas.EventGraph Player L} {prior later : graph.EventId}
    (depends : graph.DependsOn prior later) : prior.val ≤ later.val := by
  induction depends with
  | refl => exact le_rfl
  | tail _ member ih => exact ih.trans (graph.order.predecessor_lt member).le

/-- Every distinct dependency of a ready event has completed. -/
theorem DependsOn.completed_of_ready {graph : Vegas.EventGraph Player L}
    {cut : graph.order.Cut} {prior event : graph.EventId}
    (depends : graph.DependsOn prior event) (different : prior ≠ event)
    (ready : cut.Ready event) : prior ∈ cut.completed := by
  cases depends with
  | refl => exact (different rfl).elim
  | tail earlier member => exact DependsOn.completed earlier (ready.2 member)

end EventGraph

end Vegas
