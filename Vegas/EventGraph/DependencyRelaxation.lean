module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Dependencies
public import Vegas.EventGraph.Dataflow
public import Vegas.EventGraph.Sequential
public import Vegas.EventGraph.RevealRelaxation
public import Vegas.EventGraph.Semantics

@[expose] public section

/-! # Composable relaxations of supplied dependencies

Reveal and binding relaxations delete only independent direct edges from the dependency choice
already supplied. They never choose a stronger order or change code, layouts or the runtime.
The filters commute and are idempotent; transitive paths may retain an event ordering after its
direct edge is deleted. Source information policies are supplied separately.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

/-- A binding node evaluates no existing field; its requested value is the new output. -/
theorem EventCode.readFields_eq_empty_of_binding
    {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}
    {output : EventField Player L} (code : EventCode layout output)
    {owner : Player} {payload : L.Ty} (binding : output = .binding owner payload) :
    code.readFields = ∅ := by
  cases code with
  | bind => rfl
  | resolve => cases binding
  | sample => cases binding

/-- Private binding events of distinct owners have no mutual evaluation reads. -/
def IndependentBindings (graph : Vegas.EventGraph Player L) (prior event : graph.EventId) : Prop :=
  ∃ (left right : Player) (leftPayload rightPayload : L.Ty),
    graph.outputLayout prior = .binding left leftPayload ∧
    graph.outputLayout event = .binding right rightPayload ∧ left ≠ right

theorem IndependentBindings.symm {graph : Vegas.EventGraph Player L} {prior event : graph.EventId}
    (independent : graph.IndependentBindings prior event) :
    graph.IndependentBindings event prior := by
  obtain ⟨left, right, leftPayload, rightPayload, leftEq, rightEq, different⟩ := independent
  exact ⟨right, left, rightPayload, leftPayload, rightEq, leftEq, different.symm⟩

theorem IndependentBindings.not_readFields {graph : Vegas.EventGraph Player L}
    {prior event : graph.EventId} (independent : graph.IndependentBindings prior event) :
    (.inr prior : graph.Field) ∉ (graph.nodes event).readFields := by
  obtain ⟨left, right, leftPayload, rightPayload, leftEq, rightEq, different⟩ := independent
  rw [(graph.nodes event).readFields_eq_empty_of_binding rightEq]
  exact Finset.notMem_empty _

theorem IndependentBindings.not_barrierRelated {graph : Vegas.EventGraph Player L}
    {prior event : graph.EventId} (independent : graph.IndependentBindings prior event) :
    ¬ ((graph.outputLayout prior).IsPublic ∨ (graph.outputLayout event).IsPublic ∨
      (graph.outputLayout prior).SameBindingOwner (graph.outputLayout event)) := by
  obtain ⟨left, right, leftPayload, rightPayload, leftEq, rightEq, different⟩ := independent
  simpa only [leftEq, rightEq, EventField.IsPublic, EventField.SameBindingOwner, false_or]
    using different

/-- Delete only independent-reveal edges from a supplied dependency choice. -/
def revealDependencies (graph : Vegas.EventGraph Player L) (dependencies : graph.Dependencies) :
    graph.Dependencies where
  predecessors event := by
    classical
    exact (dependencies.predecessors event).filter fun prior =>
      ¬ graph.IndependentReveals prior event
  predecessor_lt := by
    classical
    intro event prior member
    exact dependencies.predecessor_lt (Finset.mem_filter.mp member).1
  reads_available := by
    classical
    intro event prior read
    refine Finset.mem_filter.mpr ⟨dependencies.reads_available event read, ?_⟩
    intro independent
    exact independent.2.2.1 ((graph.mem_readPredecessors prior event).mp read)

/-- Delete only independent-private-binding edges from a supplied dependency choice. -/
def bindingDependencies (graph : Vegas.EventGraph Player L) (dependencies : graph.Dependencies) :
    graph.Dependencies where
  predecessors event := by
    classical
    exact (dependencies.predecessors event).filter fun prior =>
      ¬ graph.IndependentBindings prior event
  predecessor_lt := by
    classical
    intro event prior member
    exact dependencies.predecessor_lt (Finset.mem_filter.mp member).1
  reads_available := by
    classical
    intro event prior read
    refine Finset.mem_filter.mpr ⟨dependencies.reads_available event read, ?_⟩
    intro independent
    exact independent.not_readFields ((graph.mem_readPredecessors prior event).mp read)

/-- Relax independent reveal edges of the supplied graph. -/
def relaxReveals (graph : Vegas.EventGraph Player L) : Vegas.EventGraph Player L :=
  graph.withDependencies (graph.revealDependencies graph.dependencies)

/-- Relax independent private-binding edges of the supplied graph. -/
def relaxBindings (graph : Vegas.EventGraph Player L) : Vegas.EventGraph Player L :=
  graph.withDependencies (graph.bindingDependencies graph.dependencies)

@[simp] theorem relaxReveals_predecessors (graph : Vegas.EventGraph Player L)
    (prior event : graph.EventId) :
    prior ∈ graph.relaxReveals.order.predecessors event ↔
      prior ∈ graph.order.predecessors event ∧ ¬ graph.IndependentReveals prior event := by
  classical
  exact Finset.mem_filter

@[simp] theorem relaxBindings_predecessors (graph : Vegas.EventGraph Player L)
    (prior event : graph.EventId) :
    prior ∈ graph.relaxBindings.order.predecessors event ↔
      prior ∈ graph.order.predecessors event ∧ ¬ graph.IndependentBindings prior event := by
  classical
  exact Finset.mem_filter

@[simp] theorem revealDependencies_withDependencies (graph : Vegas.EventGraph Player L)
    (chosen dependencies : graph.Dependencies) :
    (graph.withDependencies chosen).revealDependencies dependencies =
      graph.revealDependencies dependencies := by
  apply EventDependencies.ext
  rfl

@[simp] theorem bindingDependencies_withDependencies (graph : Vegas.EventGraph Player L)
    (chosen dependencies : graph.Dependencies) :
    (graph.withDependencies chosen).bindingDependencies dependencies =
      graph.bindingDependencies dependencies := by
  apply EventDependencies.ext
  rfl

@[simp] theorem revealDependencies_idem (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    graph.revealDependencies (graph.revealDependencies dependencies) =
      graph.revealDependencies dependencies := by
  classical
  apply EventDependencies.ext
  funext event
  ext prior
  simp only [revealDependencies, Finset.mem_filter, and_assoc, and_self]

@[simp] theorem bindingDependencies_idem (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    graph.bindingDependencies (graph.bindingDependencies dependencies) =
      graph.bindingDependencies dependencies := by
  classical
  apply EventDependencies.ext
  funext event
  ext prior
  simp only [bindingDependencies, Finset.mem_filter, and_assoc, and_self]

theorem revealDependencies_bindingDependencies (graph : Vegas.EventGraph Player L)
    (dependencies : graph.Dependencies) :
    graph.revealDependencies (graph.bindingDependencies dependencies) =
      graph.bindingDependencies (graph.revealDependencies dependencies) := by
  classical
  apply EventDependencies.ext
  funext event
  ext prior
  simp only [revealDependencies, bindingDependencies, Finset.mem_filter]
  exact and_right_comm

@[simp] theorem relaxReveals_idem (graph : Vegas.EventGraph Player L) :
    graph.relaxReveals.relaxReveals = graph.relaxReveals := by
  simp only [relaxReveals, dependencies_withDependencies, revealDependencies_withDependencies,
    withDependencies_replace, revealDependencies_idem]

@[simp] theorem relaxBindings_idem (graph : Vegas.EventGraph Player L) :
    graph.relaxBindings.relaxBindings = graph.relaxBindings := by
  simp only [relaxBindings, dependencies_withDependencies, bindingDependencies_withDependencies,
    withDependencies_replace, bindingDependencies_idem]

/-- Independent-binding and independent-reveal edge deletion commute. -/
theorem relaxReveals_relaxBindings (graph : Vegas.EventGraph Player L) :
    graph.relaxReveals.relaxBindings = graph.relaxBindings.relaxReveals := by
  simp only [relaxReveals, relaxBindings, dependencies_withDependencies,
    revealDependencies_withDependencies, bindingDependencies_withDependencies,
    withDependencies_replace, revealDependencies_bindingDependencies]

@[simp] theorem relaxReveals_inputCount (graph : Vegas.EventGraph Player L) :
    graph.relaxReveals.inputCount = graph.inputCount := rfl

@[simp] theorem relaxBindings_inputCount (graph : Vegas.EventGraph Player L) :
    graph.relaxBindings.inputCount = graph.inputCount := rfl

@[simp] theorem relaxReveals_eventCount (graph : Vegas.EventGraph Player L) :
    graph.relaxReveals.order.eventCount = graph.order.eventCount := rfl

@[simp] theorem relaxBindings_eventCount (graph : Vegas.EventGraph Player L) :
    graph.relaxBindings.order.eventCount = graph.order.eventCount := rfl

@[simp] theorem relaxReveals_inputLayout (graph : Vegas.EventGraph Player L)
    (input : graph.InputId) :
    graph.relaxReveals.inputLayout input = graph.inputLayout input := rfl

@[simp] theorem relaxBindings_inputLayout (graph : Vegas.EventGraph Player L)
    (input : graph.InputId) :
    graph.relaxBindings.inputLayout input = graph.inputLayout input := rfl

@[simp] theorem relaxReveals_outputLayout (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.relaxReveals.outputLayout event = graph.outputLayout event := rfl

@[simp] theorem relaxBindings_outputLayout (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.relaxBindings.outputLayout event = graph.outputLayout event := rfl

@[simp] theorem relaxReveals_nodes (graph : Vegas.EventGraph Player L) (event : graph.EventId) :
    graph.relaxReveals.nodes event = graph.nodes event := rfl

@[simp] theorem relaxBindings_nodes (graph : Vegas.EventGraph Player L) (event : graph.EventId) :
    graph.relaxBindings.nodes event = graph.nodes event := rfl

@[simp] theorem relaxReveals_payoffs (graph : Vegas.EventGraph Player L) :
    graph.relaxReveals.payoffs = graph.payoffs := rfl

@[simp] theorem relaxBindings_payoffs (graph : Vegas.EventGraph Player L) :
    graph.relaxBindings.payoffs = graph.payoffs := rfl

@[simp] theorem relaxReveals_finiteActions_iff (graph : Vegas.EventGraph Player L) :
    graph.relaxReveals.FiniteActions ↔ graph.FiniteActions := Iff.rfl

@[simp] theorem relaxBindings_finiteActions_iff (graph : Vegas.EventGraph Player L) :
    graph.relaxBindings.FiniteActions ↔ graph.FiniteActions := Iff.rfl

@[simp] theorem relaxReveals_sequentialize (graph : Vegas.EventGraph Player L) :
    graph.relaxReveals.sequentialize = graph.sequentialize :=
  graph.withDependencies_sequentialize _

@[simp] theorem relaxBindings_sequentialize (graph : Vegas.EventGraph Player L) :
    graph.relaxBindings.sequentialize = graph.sequentialize :=
  graph.withDependencies_sequentialize _

theorem relaxReveals_predecessors_subset (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.relaxReveals.order.predecessors event ⊆ graph.order.predecessors event := by
  intro prior member
  exact ((graph.relaxReveals_predecessors prior event).mp member).1

theorem relaxBindings_predecessors_subset (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.relaxBindings.order.predecessors event ⊆ graph.order.predecessors event := by
  intro prior member
  exact ((graph.relaxBindings_predecessors prior event).mp member).1

theorem dataflow_predecessors_subset_relaxReveals (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.dataflow.order.predecessors event ⊆ graph.relaxReveals.order.predecessors event :=
  graph.readDependencies_predecessors_subset graph.relaxReveals.dependencies event

theorem dataflow_predecessors_subset_relaxBindings (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.dataflow.order.predecessors event ⊆ graph.relaxBindings.order.predecessors event :=
  graph.readDependencies_predecessors_subset graph.relaxBindings.dependencies event

theorem combinedRelaxation_predecessors_subset (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.relaxReveals.relaxBindings.order.predecessors event ⊆ graph.order.predecessors event :=
  (graph.relaxReveals.relaxBindings_predecessors_subset event).trans
    (graph.relaxReveals_predecessors_subset event)

theorem dataflow_predecessors_subset_combinedRelaxation (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) :
    graph.dataflow.order.predecessors event ⊆
      graph.relaxReveals.relaxBindings.order.predecessors event :=
  graph.readDependencies_predecessors_subset graph.relaxReveals.relaxBindings.dependencies event

variable [DecidableEq Player]

/-- Reveal relaxation retains the reveal-relaxed public-barrier discipline. -/
theorem relaxReveals_revealRelaxedOrdered (graph : Vegas.EventGraph Player L)
    (ordered : graph.RevealRelaxedOrdered) : graph.relaxReveals.RevealRelaxedOrdered := by
  intro event prior member dependent
  exact (graph.relaxReveals_predecessors prior event).mpr
    ⟨ordered event prior member dependent, dependent⟩

/-- Binding relaxation preserves every public-barrier dependency. -/
theorem relaxBindings_barrierOrdered (graph : Vegas.EventGraph Player L)
    (ordered : graph.BarrierOrdered) : graph.relaxBindings.BarrierOrdered := by
  intro event prior member
  exact (graph.relaxBindings_predecessors prior event).mpr
    ⟨ordered event member, fun independent =>
      independent.not_barrierRelated ((mem_barrierOrder graph.outputLayout prior event).mp
        member).2⟩

/-- Binding relaxation also preserves the reveal-relaxed public-barrier discipline. -/
theorem relaxBindings_revealRelaxedOrdered (graph : Vegas.EventGraph Player L)
    (ordered : graph.RevealRelaxedOrdered) : graph.relaxBindings.RevealRelaxedOrdered := by
  intro event prior member dependent
  exact (graph.relaxBindings_predecessors prior event).mpr
    ⟨ordered event prior member dependent, fun independent =>
      independent.not_barrierRelated ((mem_barrierOrder graph.outputLayout prior event).mp
        member).2⟩

end Vegas.EventGraph
