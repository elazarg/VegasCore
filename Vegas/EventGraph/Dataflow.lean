module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Dependencies

@[expose] public section

/-! # Exact dataflow dependencies

The dataflow specialization retains the graph's typed fields, code and payoffs.
Its direct predecessors are exactly the event-output fields in each node's
declared read footprint. Information-order constraints belong to stronger
dependency specializations.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

/-- The least dependency relation making each declared event-output read
available. -/
def readDependencies (graph : Vegas.EventGraph Player L) : graph.Dependencies where
  predecessors := graph.readPredecessors
  predecessor_lt := by
    intro event producer member
    exact graph.order.predecessor_lt
      (graph.reads_available event (.inr producer)
        ((graph.mem_readPredecessors producer event).mp member))
  reads_available _ := Finset.Subset.refl _

/-- Every admissible dependency choice contains the exact producer reads. -/
theorem readDependencies_predecessors_subset (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) (event : graph.EventId) :
    graph.readDependencies.predecessors event ⊆ dependencies.predecessors event :=
  dependencies.reads_available event

/-- Retain exactly the direct producer dependencies declared by each node. -/
def dataflow (graph : Vegas.EventGraph Player L) : Vegas.EventGraph Player L :=
  graph.withDependencies graph.readDependencies

@[simp] theorem dataflow_inputCount (graph : Vegas.EventGraph Player L) :
    graph.dataflow.inputCount = graph.inputCount := rfl

@[simp] theorem dataflow_eventCount (graph : Vegas.EventGraph Player L) :
    graph.dataflow.order.eventCount = graph.order.eventCount := rfl

@[simp] theorem dataflow_inputLayout (graph : Vegas.EventGraph Player L)
    (input : graph.InputId) :
    graph.dataflow.inputLayout input = graph.inputLayout input := rfl

@[simp] theorem dataflow_outputLayout (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.dataflow.outputLayout event = graph.outputLayout event := rfl

@[simp] theorem dataflow_nodes (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.dataflow.nodes event = graph.nodes event := rfl

@[simp] theorem dataflow_payoffs (graph : Vegas.EventGraph Player L) :
    graph.dataflow.payoffs = graph.payoffs := rfl

/-- A dataflow edge is precisely an event-output read of its target node. -/
@[simp] theorem mem_dataflow_predecessors (graph : Vegas.EventGraph Player L)
    (producer event : graph.EventId) :
    producer ∈ graph.dataflow.order.predecessors event ↔
      (.inr producer : graph.Field) ∈ (graph.nodes event).readFields := by
  classical
  exact graph.mem_readPredecessors producer event

/-- Every structurally valid graph already contains all of its dataflow edges. -/
theorem dataflow_predecessors_subset (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.dataflow.order.predecessors event ⊆ graph.order.predecessors event := by
  intro producer member
  exact graph.reads_available event (.inr producer)
    ((graph.mem_dataflow_predecessors producer event).mp member)

/-- Removing information-order edges twice has the same effect as removing
them once. -/
@[simp] theorem dataflow_idem (graph : Vegas.EventGraph Player L) :
    graph.dataflow.dataflow = graph.dataflow := by
  cases graph
  rfl

/-- Replacing information-order constraints leaves the dataflow graph
unchanged. -/
@[simp] theorem withDependencies_dataflow (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    (graph.withDependencies dependencies).dataflow = graph.dataflow := by
  cases graph
  rfl

end Vegas.EventGraph
