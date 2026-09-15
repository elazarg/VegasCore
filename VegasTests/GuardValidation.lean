/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GuardValidation
import Vegas.Compile.SealedGuardValidation
import Vegas.Core.ExprSimple

/-! # Nontrivial guard checks without unused private choice information -/

namespace VegasTests.GuardValidation

open Vegas Vegas.EventGraph
open Interaction Interaction.MessageApplication GameTheory.Math.Probability

private def fields {name : VarId} {ty : BaseTy} :
    HasVar [(10, .bool), (11, .bool)] name ty → Nat
  | .here => 0
  | .there .here => 1

private def publicGuard : EventGuard simpleExpr where
  ty := .option .bool
  code := {
    actionName := 12
    Context := [(10, .bool), (11, .bool)]
    expr := Expr.nullableCommitGuard
      (.andBool (.var 12 .here) (.var 11 (.there (.there .here))))
    fieldOf := fields }
  choiceReads := {⟨0, .bool⟩, ⟨1, .bool⟩}
  read_mem binding := by
    cases binding with
    | here => simp [GuardCode.ref, fields]
    | there binding =>
        cases binding with
        | here => simp [GuardCode.ref, fields]
        | there binding => cases binding

private def graph : Graph Nat simpleExpr where
  initialFields := [⟨.bool, some 0, false⟩, ⟨.bool, none, true⟩]
  nodes := [⟨.option .bool, some 0, .commit 0 publicGuard⟩,
    ⟨.option .bool, none, .reveal 2⟩]

private def publicStore (value : Bool) : Store simpleExpr :=
  fun field => if field = 1 then some ⟨.bool, value⟩ else none

/-- The player sees a private earlier choice, but the guard only needs the
public field in addition to the proposed action. -/
theorem validation_omits_private_choice :
    publicGuard.choiceReads = {⟨0, .bool⟩, ⟨1, .bool⟩} ∧
      publicGuard.validationReads = {⟨1, .bool⟩} := by
  constructor
  · rfl
  · decide

theorem public_guard_eligible : publicGuard.PubliclyValidatable graph := by
  intro ref href
  rw [validation_omits_private_choice.2] at href
  have heq := Finset.mem_singleton.mp href
  subst ref
  norm_num [Graph.fieldRefPublic, Graph.field?, graph]

/-- No private stored value is supplied to these nontrivial acceptance tests. -/
theorem public_guard_checks :
    publicStore true 0 = none ∧
      publicGuard.evalValidationStore? (some true) (publicStore true) = some true ∧
      publicGuard.evalValidationStore? (some false) (publicStore true) = some false ∧
      publicGuard.evalValidationStore? (some true) (publicStore false) = some false ∧
      publicGuard.evalValidationStore? none (publicStore false) = some true := by
  decide

/-- Missing a real dependency is distinguished from a successfully evaluated,
rejecting guard. -/
theorem missing_public_dependency_rejects_evaluation :
    publicGuard.evalValidationStore? (some true) (fun _ => none) = none := by
  decide

private def privateGuard : EventGuard simpleExpr :=
  { publicGuard with code := { publicGuard.code with
      expr := Expr.nullableCommitGuard
        (.andBool (.var 12 .here) (.var 10 (.there .here))) } }

/-- A genuinely private guard dependency is not admitted by the public-check
predicate. Supporting it requires another validation mechanism or disclosure. -/
theorem private_guard_ineligible : ¬ privateGuard.PubliclyValidatable graph := by
  intro h
  have hread : (⟨0, .bool⟩ : FieldRef simpleExpr) ∈ privateGuard.validationReads := by decide
  have hpublic := h _ hread
  norm_num [Graph.fieldRefPublic, Graph.field?, graph] at hpublic
  cases hpublic

private def runtime : SealedResolution Nat (Option Bool) :=
  ⟨⟨graph.nodeOrder.map graph.sealedRule⟩, none, 2⟩

private noncomputable def app : MessageApplication Nat :=
  runtime.guardedCandidateApplication (graph.sealedOpeningValidator (.option .bool))

private noncomputable def initial : app.State :=
  State.initial app runtime.candidateInitial

private noncomputable def openingTrace (value : Option Bool) : List app.Action :=
  [.privateCommand 0 ⟨(7, value)⟩,
    .submit 0 (.commitment 0 (0, 7)), .include (0, 0),
    .submit 0 (.opening 1 (0, 7) value), .deliver 1 (0, 1), .include (0, 1)]

/-- The retained graph guard compiles to a real public validation callback:
the invalid Boolean candidate is rejected, and legal participation or quitting
values satisfy the same check. -/
theorem compiled_opening_checks :
    graph.sealedOpeningValidator (.option .bool) 1 [] (some false) = false ∧
      graph.sealedOpeningValidator (.option .bool) 1 [] (some true) = true ∧
      graph.sealedOpeningValidator (.option .bool) 1 [] none = true := by
  decide

/-- Guard validation is not performed at commitment acceptance: even the
guard-invalid candidate reaches a selected opaque handle. -/
theorem invalid_candidate_is_selected :
    (app.run ((openingTrace (some false)).take 3) initial).map
      (fun next => next.application.visible.events) =
      FinDist.pure [SealedProgram.Event.accepted 0 (0, 7)] := by
  simp only [openingTrace, List.take_succ_cons, List.take_zero,
    MessageApplication.run, MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- An invalid opening remains visible in the recipient's inbox and receives
a rejection receipt. The shared clock subsequently publishes the null default;
the original private candidate meaning remains fixed. -/
theorem rejected_opening_times_out :
    (app.run (openingTrace (some false) ++ [.environment ⟨()⟩, .environment ⟨()⟩]) initial).map
      (fun next => (next.application.visible.events, next.receipts,
        next.pool.inbox 1, next.application.service.lookup (0, 7))) =
      FinDist.pure
        ([SealedProgram.Event.accepted 0 (0, 7), .opened 1 none],
          [((0, 0), true), ((0, 1), false)],
          [⟨(0, 1), .opening 1 (0, 7) (some false)⟩],
          CommitmentCandidate.openable (some false)) := by
  simp only [openingTrace, List.cons_append, List.nil_append,
    MessageApplication.run, MessageApplication.step, FinDist.pure_bind]
  simp only [app, SealedResolution.guardedCandidateApplication, SealedResolution.host,
    FinDist.map_pure, FinDist.pure_bind]
  rfl

/-- A legal opening is included with a positive receipt and no timeout. -/
theorem legal_opening_is_included :
    (app.run (openingTrace (some true)) initial).map
      (fun next => (next.application.visible.events, next.receipts,
        next.application.visible.timeouts)) =
      FinDist.pure
        ([SealedProgram.Event.accepted 0 (0, 7), .opened 1 (some true)],
          [((0, 0), true), ((0, 1), true)], ([] : List Nat)) := by
  simp only [openingTrace, MessageApplication.run, MessageApplication.step,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

end VegasTests.GuardValidation
