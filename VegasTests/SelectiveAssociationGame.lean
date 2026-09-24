/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocolBehavioral
import Vegas.Compile.EventGraphAssembly
import Vegas.Expr.Simple

/-! # The source game for selective association

Alice binds a Boolean; Carol and Bob bind guesses. Ordinary disclosures follow
in that order. Utilities depend only on these three public results. Each player
loses four units when its own publication fails, so successful disclosure can
be proved preferable without replacing it by an automatic opening operation.

This module supplies the shared program and payoff carrier. Communication
services, assessments, and their equilibrium claims are separate obligations.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

abbrev Player := Fin 3
abbrev alice : Player := 0
abbrev bob : Player := 1
abbrev carol : Player := 2

def acceptingGuard {context : SourceCtx Player simpleExpr} (owner : Player) (name : VarId) :
    SourceGuard simpleExpr context owner name .bool where
  schema := []
  schemaNames := by simp
  subjectFresh := by simp
  code := .constBool true
  reads := fun ref => nomatch ref

/-- The settlement sees exactly the three public publication results. -/
abbrev PayoffCtx : CtxSimple :=
  [(5, .result .bool), (4, .result .bool), (3, .result .bool)]

def correctnessExpr (reward : Int) (value guess : Expr PayoffCtx (.result .bool)) :
    Expr PayoffCtx .int :=
  .ite (.andBool (.andBool (.isSuccess value) (.isSuccess guess))
      (.eq (.getResultD value (.constBool false)) (.getResultD guess (.constBool false))))
    (.constInt reward) (.constInt 0)

def failureExpr (value : Expr PayoffCtx (.result .bool)) : Expr PayoffCtx .int :=
  .ite (.isFailure value) (.constInt (-4)) (.constInt 0)

/-- The analyzed preferences are literal signed integer settlement payoffs. -/
def payoffExpr (who : Player) : Expr PayoffCtx .int :=
  let a : Expr PayoffCtx (.result .bool) := .var 3 (.there (.there .here))
  let b : Expr PayoffCtx (.result .bool) := .var 5 .here
  let c : Expr PayoffCtx (.result .bool) := .var 4 (.there .here)
  if who = alice then
    .addInt (.addInt (correctnessExpr 1 a b) (correctnessExpr (-1) a c)) (failureExpr a)
  else if who = bob then
    .addInt (correctnessExpr 1 a b) (failureExpr b)
  else
    .addInt (correctnessExpr 1 a c) (failureExpr c)

def sourceProgram : SourceProgram Player simpleExpr [] ∅ :=
  .commit 0 alice (by decide) (acceptingGuard alice 0) <|
  .commit 1 carol (by decide) (acceptingGuard carol 1) <|
  .commit 2 bob (by decide) (acceptingGuard bob 2) <|
  .reveal 3 alice 0 (by decide) (.there (.there .here)) (by decide) <|
  .reveal 4 carol 1 (by decide) (.there (.there .here)) (by decide) <|
  .reveal 5 bob 2 (by decide) (.there (.there .here)) (by decide) <|
  .ret [(alice, payoffExpr alice), (bob, payoffExpr bob), (carol, payoffExpr carol)]

def sourceSetup : Setup (Player := Player) (L := simpleExpr) where
  context := []
  namesNodup := by simp
  initialLaw := FinDist.pure (Env.empty _)
  obligations := ∅
  program := sourceProgram
  accounts := rfl

def sourceAdmission : CommitmentInterface sourceSetup.program :=
  CommitmentInterface.forfeiture sourceProgram

abbrev nativeGraph := sourceSetup.eventGraph

abbrev aliceBinding : nativeGraph.EventId := ⟨0, by decide⟩
abbrev carolBinding : nativeGraph.EventId := ⟨1, by decide⟩
abbrev bobBinding : nativeGraph.EventId := ⟨2, by decide⟩
abbrev alicePublication : nativeGraph.EventId := ⟨3, by decide⟩
abbrev carolPublication : nativeGraph.EventId := ⟨4, by decide⟩
abbrev bobPublication : nativeGraph.EventId := ⟨5, by decide⟩

/-- The utility carrier contains only original public source results. -/
structure Results where
  alice : PublicationResult Bool
  bob : PublicationResult Bool
  carol : PublicationResult Bool
  deriving DecidableEq

def sourceResults (state : State simpleExpr sourceProgram.terminalCtx) : Results where
  alice := state.get (.there (.there .here))
  bob := state.get .here
  carol := state.get (.there .here)

def correctness : PublicationResult Bool → PublicationResult Bool → ℝ
  | .success value, .success guess => if value = guess then 1 else 0
  | _, _ => 0

def openingPenalty : PublicationResult Bool → ℝ
  | .success _ => 0
  | .failure => 4

def utility (result : Results) (who : Player) : ℝ :=
  if who = alice then
    correctness result.alice result.bob - correctness result.alice result.carol -
      openingPenalty result.alice
  else if who = bob then
    correctness result.alice result.bob - openingPenalty result.bob
  else
    correctness result.alice result.carol - openingPenalty result.carol

/-- The fixed utility is the program's returned integer payoff, not an
additional preference over network traces or private data. -/
theorem payoffExpr_eq_utility (env : PlainEnv PayoffCtx) (who : Player) :
    (evalExpr (payoffExpr who) env : ℝ) =
      utility ⟨env.get (.there (.there .here)), env.get .here, env.get (.there .here)⟩ who := by
  generalize ha : env.get (.there (.there .here)) = a
  generalize hb : env.get .here = b
  generalize hc : env.get (.there .here) = c
  fin_cases who <;>
    simp [payoffExpr, alice, bob, utility, correctnessExpr, failureExpr, evalExpr,
      ha, hb, hc]
  all_goals cases a <;> cases b <;> cases c
  all_goals simp_all [correctness, openingPenalty, PublicationResult.isSuccess,
    PublicationResult.isFailure, PublicationResult.getD]
  all_goals split_ifs <;> norm_num

theorem source_settlement_eq_utility (state : State simpleExpr sourceProgram.terminalCtx) :
    (sourceProgram.evaluatePayoffs state).map (fun payoff => (payoff.1, (payoff.2 : ℝ))) =
      [(alice, utility (sourceResults state) alice),
        (bob, utility (sourceResults state) bob),
        (carol, utility (sourceResults state) carol)] := by
  change [(alice, (evalExpr (payoffExpr alice) (sourcePublicEnv state) : ℝ)),
    (bob, (evalExpr (payoffExpr bob) (sourcePublicEnv state) : ℝ)),
    (carol, (evalExpr (payoffExpr carol) (sourcePublicEnv state) : ℝ))] = _
  rw [payoffExpr_eq_utility, payoffExpr_eq_utility, payoffExpr_eq_utility]
  rfl

@[simp] theorem utility_alice (result : Results) :
    utility result alice = correctness result.alice result.bob -
      correctness result.alice result.carol - openingPenalty result.alice := rfl

@[simp] theorem utility_bob (result : Results) :
    utility result bob = correctness result.alice result.bob - openingPenalty result.bob := rfl

@[simp] theorem utility_carol (result : Results) :
    utility result carol = correctness result.alice result.carol -
      openingPenalty result.carol := rfl

@[simp] theorem correctness_success_self (value : Bool) :
    correctness (.success value) (.success value) = 1 := by simp [correctness]

@[simp] theorem correctness_failure_left (guess : PublicationResult Bool) :
    correctness .failure guess = 0 := by cases guess <;> rfl

@[simp] theorem correctness_failure_right (value : PublicationResult Bool) :
    correctness value .failure = 0 := by cases value <;> rfl

@[simp] theorem openingPenalty_success (value : Bool) : openingPenalty (.success value) = 0 := rfl
@[simp] theorem openingPenalty_failure : openingPenalty .failure = 4 := rfl

end VegasTests.SelectiveAssociation
