/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCompiler
import Vegas.Game.SealedRelease

/-! # A multistage checked source in the sealed-message backend

The same player commits again after its first reveal. The second source
decision sees both the earlier private binding and its public alias. Both
commitments still use opaque messages; information reads do not require
runtime guard evaluation when the guard accepts every value.
-/

noncomputable section

namespace VegasTests.PendingStages

open Vegas Vegas.EventGraph Interaction

abbrev Player := Fin 1
abbrev Value := Option Bool

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (b := .option .bool)
    (Expr.nullableCommitGuard (Expr.constBool true))
    (.reveal 1 0 0 .here
      (.commit 2 0 (b := .option .bool)
        (Expr.nullableCommitGuard (Expr.constBool true))
        (.reveal 3 0 2 .here (.ret []))))

def source : WFProgram Player simpleExpr where
  core := {
    Γ := []
    prog := core
    env := VEnv.empty simpleExpr
    wctx := by simp
    fresh := by simp [core, FreshBindings, Fresh] }
  accounted := CommitmentAccounting.ofRevealComplete core
    (by simp [core, FreshBindings, Fresh]) [] (by simp) (by decide)
  legal := by
    unfold core
    constructor
    · intro env
      exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
    · constructor
      · intro env
        exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
      · trivial

abbrev compiled := ToEventGraph.compile source.core
abbrev graph := compiled.graph

def node (index : Fin 4) : Fin graph.nodeCount := index

theorem supported : SealedFragment graph (.option .bool) where
  graphWF := compiled.graphWF
  rowType node := by fin_cases node <;> rfl
  noSamples node dist := by fin_cases node <;> intro h <;> cases h
  commitType node who guard hsem := by fin_cases node <;> cases hsem <;> rfl
  commitGuard node who guard hsem value env := by
    fin_cases node <;> cases hsem <;> cases value <;> rfl
  revealSource node sourceField hsem := by
    fin_cases node
    · cases hsem
    · cases hsem; exact ⟨node 0, 0, _, rfl, rfl⟩
    · cases hsem
    · cases hsem; exact ⟨node 2, 0, _, rfl, rfl⟩

/-- Admission genuinely includes a decision with a nonempty information set. -/
theorem second_choice_reads :
    ∃ guard, (graph.nodeRow (node 2)).sem = .commit 0 guard ∧
      guard.choiceReads.Nonempty := by
  refine ⟨_, rfl, ?_⟩
  change (insert {field := 1, ty := .option .bool}
    (insert {field := 0, ty := .option .bool} ∅) : Finset (FieldRef simpleExpr)).Nonempty
  exact Finset.insert_nonempty _ _

theorem second_choice_prerequisites : graph.prereqs (node 2) = {node 0, node 1} := by decide

def program : SealedProgram Player := supported.compile

def actions (first second : Value) : List (SealedProgram.Action Player Value) :=
  [.register 0 0 first, .submit 0 (.commitment 0 (0, 0)), .include (0, 0),
   .submit 0 (.opening 1 (0, 0) first), .deliver 0 (0, 1), .include (0, 1),
   .register 0 2 second, .submit 0 (.commitment 2 (0, 2)), .include (0, 2),
   .submit 0 (.opening 3 (0, 2) second), .deliver 0 (0, 3), .include (0, 3)]

/-- Both source stages execute through the same native pool and sealed rules. -/
theorem run_events (first second : Value) :
    (program.run (SealedProgram.State.empty Player Value) (actions first second)).events =
      [.accepted 0 (0, 0), .opened 1 first, .accepted 2 (0, 2), .opened 3 second] := by
  fin_cases first <;> fin_cases second <;> rfl

/-- The general arbitrary-traffic source theorem applies to this checked
multistage source, not just to its demonstrated transcript. -/
theorem native_prefix (traffic : List (SealedProgram.Action Player Value)) :
    ∃ cfg : Config graph,
      graph.decodeSealed (.option .bool)
        (program.run (SealedProgram.State.empty Player Value) traffic) = some cfg ∧
      Reachable graph cfg := by
  obtain ⟨cfg, hdecode, hreachable, _hterminal⟩ :=
    source.sealed_run_source (.option .bool) supported traffic
  exact ⟨cfg, hdecode, hreachable⟩

end VegasTests.PendingStages

/-- info: 'VegasTests.PendingStages.native_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingStages.native_prefix
