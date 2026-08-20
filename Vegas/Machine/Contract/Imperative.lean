/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.Validator
import Vegas.EventGraph.FiniteState

/-!
# Ordered imperative contract requirements

This lowering introduces one operational detail: graph readiness becomes an
ordered list of runtime requirements. Each action first checks that it has not
already completed and then checks its prerequisites in the canonical order of
the prerequisite `Finset`.

The order has no semantic effect at this pass because requirements are pure
Boolean reads. Later backends may expose order through gas use or revert data;
that observation change must be analyzed where it is introduced.
-/

namespace Vegas.Machine.Contract.Imperative

open EventGraph

noncomputable section

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- One pure control-flow requirement emitted before an action body. -/
inductive Requirement (program : Program Player L) where
  | notCompleted (node : Fin program.graph.nodeCount)
  | completed (node : Fin program.graph.nodeCount)

namespace Requirement

/-- Evaluate one requirement against semantic graph configuration state. -/
def evaluate (cfg : Config program.graph) : Requirement program → Bool
  | .notCompleted node => decide (node ∉ cfg.done)
  | .completed node => decide (node ∈ cfg.done)

end Requirement

/-- Sequentially evaluate all requirements, stopping at the first failure in
an imperative backend even though this functional definition is pure. -/
def evaluateAll (cfg : Config program.graph)
    (requirements : List (Requirement program)) : Bool :=
  requirements.all (Requirement.evaluate cfg)

/-- Canonical ordered requirements for one graph action. -/
def requirements (program : Program Player L)
    (node : Fin program.graph.nodeCount) : List (Requirement program) :=
  .notCompleted node ::
    (program.graph.prereqs node).toList.map Requirement.completed

/-- The ordered imperative requirements accept exactly ready graph nodes. -/
theorem evaluateAll_requirements_eq_true_iff
    (cfg : Config program.graph)
    (node : Fin program.graph.nodeCount) :
    evaluateAll cfg (requirements program node) = true ↔
      Ready program.graph cfg node := by
  have hsubset :
      (∀ prior, prior ∈ program.graph.prereqs node → prior ∈ cfg.done) ↔
        program.graph.prereqs node ⊆ cfg.done := by
    constructor
    · intro hall prior hprior
      exact hall prior hprior
    · intro subset prior hprior
      exact subset hprior
  simp [evaluateAll, requirements, Requirement.evaluate, Ready, hsubset]

/-- Executable Boolean equality between ordered requirements and readiness. -/
theorem evaluateAll_requirements
    (cfg : Config program.graph)
    (node : Fin program.graph.nodeCount) :
    evaluateAll cfg (requirements program node) =
      decide (Ready program.graph cfg node) := by
  apply Bool.eq_iff_iff.mpr
  rw [evaluateAll_requirements_eq_true_iff]
  simp

/-- One action in the first imperative contract IR. Expression and event code
remain in the source-independent machine row while layout and control checks
are made explicit. -/
structure ActionIR (program : Program Player L) where
  node : Fin program.graph.nodeCount
  authority : Authority Player
  inputType : Option L.Ty
  outputSlot : Nat
  requirements : List (Requirement program)
  row : EventNode Player L

/-- Lower one stable graph action using the chosen certified storage layout. -/
def compileAction (layout : Layout program)
    (node : Fin program.graph.nodeCount) : ActionIR program where
  node := node
  authority := Action.authority program ⟨node⟩
  inputType := Action.inputType program ⟨node⟩
  outputSlot := layout.address
    (.value
      ⟨program.graph.nodeTarget node,
        Vegas.EventGraph.StateSnapshot.nodeTarget_lt_fieldCount
          program.graph node⟩)
  requirements := Imperative.requirements program node
  row := program.graph.nodeRow node

/-- Whole imperative contract inventory. Action order is the graph's stable
canonical node order; each action carries its ordered requirements. -/
structure ContractIR (program : Program Player L) where
  storageSize : Nat
  actions : List (ActionIR program)

/-- Compile the machine manifest and a chosen physical layout to the first
imperative contract IR. -/
def compile (program : Program Player L) (layout : Layout program) :
    ContractIR program where
  storageSize := layout.slotCount
  actions := program.graph.nodeOrder.map (compileAction layout)

@[simp] theorem compile_actions_length (layout : Layout program) :
    (compile program layout).actions.length = program.graph.nodeCount := by
  simp [compile, Graph.nodeOrder]

/-- Every graph node has its compiled action in the imperative inventory. -/
theorem compileAction_mem (layout : Layout program)
    (node : Fin program.graph.nodeCount) :
    compileAction layout node ∈ (compile program layout).actions := by
  simp [compile, Graph.mem_nodeOrder]

@[simp] theorem compileAction_requirements (layout : Layout program)
    (node : Fin program.graph.nodeCount) :
    (compileAction layout node).requirements = requirements program node :=
  rfl

/-- Compiled control requirements retain exactly the graph readiness check. -/
theorem compileAction_requirements_correct (layout : Layout program)
    (cfg : Config program.graph)
    (node : Fin program.graph.nodeCount) :
    evaluateAll cfg (compileAction layout node).requirements =
      decide (Ready program.graph cfg node) :=
  evaluateAll_requirements cfg node

end

end Vegas.Machine.Contract.Imperative
