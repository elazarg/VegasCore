module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Sequential
public import Vegas.EventGraph.Semantics

@[expose] public section

/-! # Dependencies for concurrent private bindings

Bindings of different owners can be unordered without changing node code or
the availability of its inputs. Public barriers and each owner's binding order
remain in place. This transformation composes with independent-reveal relaxation.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
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

/-- Private bindings of distinct owners may complete independently. -/
def IndependentBindings (graph : Vegas.EventGraph Player L) (prior event : graph.EventId) : Prop :=
  ∃ (left right : Player) (leftPayload rightPayload : L.Ty),
    graph.outputLayout prior = .binding left leftPayload ∧
    graph.outputLayout event = .binding right rightPayload ∧ left ≠ right

variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
theorem IndependentBindings.symm {prior event : graph.EventId}
    (independent : graph.IndependentBindings prior event) :
    graph.IndependentBindings event prior := by
  obtain ⟨left, right, leftPayload, rightPayload, leftEq, rightEq, different⟩ := independent
  exact ⟨right, left, rightPayload, leftPayload, rightEq, leftEq, different.symm⟩

omit [DecidableEq Player] in
/-- An independently concurrent binding cannot read its peer's output. -/
theorem IndependentBindings.not_readFields {prior event : graph.EventId}
    (independent : graph.IndependentBindings prior event) :
    (.inr prior : graph.Field) ∉ (graph.nodes event).readFields := by
  obtain ⟨left, right, leftPayload, rightPayload, leftEq, rightEq, different⟩ := independent
  rw [(graph.nodes event).readFields_eq_empty_of_binding rightEq]
  exact Finset.notMem_empty _

omit [DecidableEq Player] in
/-- Dropped binding dependencies were never public-barrier dependencies. -/
theorem IndependentBindings.not_barrierRelated {prior event : graph.EventId}
    (independent : graph.IndependentBindings prior event) :
    ¬ ((graph.outputLayout prior).IsPublic ∨ (graph.outputLayout event).IsPublic ∨
      (graph.outputLayout prior).SameBindingOwner (graph.outputLayout event)) := by
  obtain ⟨left, right, leftPayload, rightPayload, leftEq, rightEq, different⟩ := independent
  simpa only [leftEq, rightEq, EventField.IsPublic, EventField.SameBindingOwner,
    false_or] using different

variable (graph)

/-- Retain every dependency except those between private bindings of distinct owners. -/
def bindingRelaxedPredecessors (event : graph.EventId) : Finset graph.EventId := by
  classical
  exact (graph.order.predecessors event).filter fun prior =>
    ¬ graph.IndependentBindings prior event

omit [DecidableEq Player] in
theorem mem_bindingRelaxedPredecessors (prior event : graph.EventId) :
    prior ∈ graph.bindingRelaxedPredecessors event ↔
      prior ∈ graph.order.predecessors event ∧ ¬ graph.IndependentBindings prior event := by
  classical
  simp only [bindingRelaxedPredecessors, Finset.mem_filter]

/-- Relax independent private bindings on the existing event graph; fields,
event code, payoffs and every evaluation dependency remain the same. -/
def withConcurrentBindings : Vegas.EventGraph Player L where
  inputCount := graph.inputCount
  order := {
    eventCount := graph.order.eventCount
    predecessors := graph.bindingRelaxedPredecessors
    predecessor_lt := by
      intro event prior member
      exact graph.order.predecessor_lt
        ((graph.mem_bindingRelaxedPredecessors prior event).mp member).1 }
  inputLayout := graph.inputLayout
  outputLayout := graph.outputLayout
  nodes := graph.nodes
  reads_available := by
    intro event field read
    cases field with
    | inl input => trivial
    | inr prior =>
        exact (graph.mem_bindingRelaxedPredecessors prior event).mpr
          ⟨graph.reads_available event (.inr prior) read,
            fun independent => independent.not_readFields read⟩
  payoffs := graph.payoffs

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_predecessors (prior event : graph.EventId) :
    prior ∈ graph.withConcurrentBindings.order.predecessors event ↔
      prior ∈ graph.order.predecessors event ∧ ¬ graph.IndependentBindings prior event :=
  graph.mem_bindingRelaxedPredecessors prior event

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_sequentialize :
    graph.withConcurrentBindings.sequentialize = graph.sequentialize := rfl

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_inputCount :
    graph.withConcurrentBindings.inputCount = graph.inputCount := rfl

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_eventCount :
    graph.withConcurrentBindings.order.eventCount = graph.order.eventCount := rfl

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_inputLayout (input : graph.InputId) :
    graph.withConcurrentBindings.inputLayout input = graph.inputLayout input := rfl

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_outputLayout (event : graph.EventId) :
    graph.withConcurrentBindings.outputLayout event = graph.outputLayout event := rfl

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_nodes (event : graph.EventId) :
    graph.withConcurrentBindings.nodes event = graph.nodes event := rfl

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_payoffs :
    graph.withConcurrentBindings.payoffs = graph.payoffs := rfl

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_finiteActions_iff :
    graph.withConcurrentBindings.FiniteActions ↔ graph.FiniteActions := Iff.rfl

/-- Private binding relaxation retains every public-barrier dependency. -/
theorem withConcurrentBindings_barrierOrdered (ordered : graph.BarrierOrdered) :
    graph.withConcurrentBindings.BarrierOrdered := by
  intro event prior member
  exact (graph.mem_bindingRelaxedPredecessors prior event).mpr
    ⟨ordered event member, fun independent =>
      independent.not_barrierRelated ((mem_barrierOrder graph.outputLayout prior event).mp
        member).2⟩

/-- Private binding relaxation also retains the weaker reveal-relaxed barrier discipline. -/
theorem withConcurrentBindings_revealRelaxedOrdered (ordered : graph.RevealRelaxedOrdered) :
    graph.withConcurrentBindings.RevealRelaxedOrdered := by
  intro event prior member dependent
  exact (graph.mem_bindingRelaxedPredecessors prior event).mpr
    ⟨ordered event prior member dependent, fun independent =>
      independent.not_barrierRelated ((mem_barrierOrder graph.outputLayout prior event).mp
        member).2⟩

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_independentReveals (prior event : graph.EventId) :
    graph.withConcurrentBindings.IndependentReveals prior event ↔
      graph.IndependentReveals prior event := Iff.rfl

omit [DecidableEq Player] in
@[simp] theorem withConcurrentBindings_withMode_concurrentReveals_predecessors
    (prior event : graph.EventId) :
    prior ∈ (graph.withConcurrentBindings.withMode .concurrentReveals).order.predecessors event ↔
      prior ∈ graph.order.predecessors event ∧
        ¬ graph.IndependentBindings prior event ∧ ¬ graph.IndependentReveals prior event := by
  rw [withMode_concurrentReveals_predecessors, withConcurrentBindings_predecessors,
    withConcurrentBindings_independentReveals]
  exact and_assoc

end Vegas.EventGraph
