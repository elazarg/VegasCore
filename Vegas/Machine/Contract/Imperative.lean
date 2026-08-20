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

/-- Observable result of short-circuit requirement evaluation. On success,
`passed` is the complete requirement list. On rejection, `passed` is exactly
the successful prefix and `failed` is the first failed requirement. Keeping
this information explicit lets a later pass state whether it exposes or hides
check order through gas use or revert data. -/
inductive CheckResult (program : Program Player L) where
  | accepted (passed : List (Requirement program))
  | rejected (passed : List (Requirement program))
      (failed : Requirement program)

namespace CheckResult

/-- Whether short-circuit evaluation accepted the requirement list. -/
def succeeded : CheckResult program → Bool
  | .accepted _ => true
  | .rejected _ _ => false

/-- Number of requirements actually evaluated. The failed requirement counts
as one evaluated check. -/
def checkedCount : CheckResult program → Nat
  | .accepted passed => passed.length
  | .rejected passed _ => passed.length + 1

end CheckResult

/-- Evaluate requirements from left to right and retain the first-failure
observation produced by an imperative backend. -/
def runChecks (cfg : Config program.graph) :
    List (Requirement program) → CheckResult program
  | [] => .accepted []
  | requirement :: rest =>
      if Requirement.evaluate cfg requirement then
        match runChecks cfg rest with
        | .accepted passed => .accepted (requirement :: passed)
        | .rejected passed failed =>
            .rejected (requirement :: passed) failed
      else
        .rejected [] requirement

/-- Retaining first-failure detail does not change whether the ordered checks
accept. -/
theorem runChecks_succeeded (cfg : Config program.graph)
    (checks : List (Requirement program)) :
    (runChecks cfg checks).succeeded = evaluateAll cfg checks := by
  induction checks with
  | nil => rfl
  | cons requirement rest ih =>
      by_cases heval : Requirement.evaluate cfg requirement = true
      · cases hrest : runChecks cfg rest with
        | accepted passed =>
            simpa [runChecks, heval, hrest, CheckResult.succeeded,
              evaluateAll] using ih
        | rejected passed failed =>
            simpa [runChecks, heval, hrest, CheckResult.succeeded,
              evaluateAll] using ih
      · have hevalFalse : Requirement.evaluate cfg requirement = false :=
          Bool.eq_false_of_not_eq_true heval
        simp [runChecks, hevalFalse, evaluateAll, CheckResult.succeeded]

/-- A rejection identifies a genuine prefix of successful checks followed by
the first failed check. -/
theorem runChecks_rejected_prefix (cfg : Config program.graph)
    {checks passed : List (Requirement program)}
    {failed : Requirement program}
    (hreject : runChecks cfg checks = .rejected passed failed) :
    ∃ remaining,
      checks = passed ++ failed :: remaining ∧
      (∀ requirement ∈ passed,
        Requirement.evaluate cfg requirement = true) ∧
      Requirement.evaluate cfg failed = false := by
  induction checks generalizing passed failed with
  | nil => simp [runChecks] at hreject
  | cons requirement rest ih =>
      by_cases heval : Requirement.evaluate cfg requirement = true
      · simp only [runChecks, heval, ↓reduceIte] at hreject
        cases hrest : runChecks cfg rest with
        | accepted restPassed => simp [hrest] at hreject
        | rejected restPassed restFailed =>
            simp only [hrest] at hreject
            cases hreject
            obtain ⟨remaining, hdecomp, hpassed, hfailed⟩ := ih hrest
            refine ⟨remaining, ?_, ?_, hfailed⟩
            · simp [hdecomp]
            · intro checked hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact heval
              · exact hpassed checked hmem
      · have hevalFalse : Requirement.evaluate cfg requirement = false :=
          Bool.eq_false_of_not_eq_true heval
        simp only [runChecks, hevalFalse, Bool.false_eq_true, ↓reduceIte] at hreject
        cases hreject
        exact ⟨rest, by simp, by simp, hevalFalse⟩

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

/-- The observable short-circuit runner accepts exactly ready graph nodes. -/
theorem runChecks_requirements_succeeded
    (cfg : Config program.graph)
    (node : Fin program.graph.nodeCount) :
    (runChecks cfg (requirements program node)).succeeded =
      decide (Ready program.graph cfg node) := by
  rw [runChecks_succeeded, evaluateAll_requirements]

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
