/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocolBehavioral
import Vegas.Compile.EventGraphAssembly
import Vegas.Expr.Simple

/-! # A guessing game with an initialized hidden commitment

Bob guesses by opening or withholding his initial commitment to `true`.
Alice subsequently chooses whether to open her fair initial bit. Successful
correct guesses reward both players; Alice loses four on opening failure.
Watcher has no source decision and receives zero.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

abbrev Player := Fin 3
abbrev alice : Player := 0
abbrev bob : Player := 1
abbrev watcher : Player := 2

abbrev initialCtx : SourceCtx Player simpleExpr :=
  [(0, .commitment alice .bool), (1, .commitment bob .bool)]

abbrev PayoffCtx : CtxSimple := [(3, .result .bool), (2, .result .bool)]

def correctnessExpr : Expr PayoffCtx .int :=
  let a : Expr PayoffCtx (.result .bool) := .var 3 .here
  let b : Expr PayoffCtx (.result .bool) := .var 2 (.there .here)
  .ite (.andBool (.isSuccess a)
    (.eq (.getResultD a (.constBool false)) (.isSuccess b))) (.constInt 1) (.constInt 0)

def payoffExpr (who : Player) : Expr PayoffCtx .int :=
  if who = alice then
    .addInt correctnessExpr
      (.ite (.isFailure (.var 3 .here)) (.constInt (-4)) (.constInt 0))
  else if who = bob then correctnessExpr else .constInt 0

def sourceProgram : SourceProgram Player simpleExpr initialCtx {0, 1} :=
  .reveal 2 bob 1 (by decide) (.there .here) (by decide) <|
  .reveal 3 alice 0 (by decide) (.there .here) (by decide) <|
  .ret [(alice, payoffExpr alice), (bob, payoffExpr bob), (watcher, payoffExpr watcher)]

def initialState (bit : Bool) : State simpleExpr initialCtx :=
  Env.cons (.success bit) <| Env.cons (.success true) <| Env.empty _

def sourceSetup : Setup (Player := Player) (L := simpleExpr) where
  context := initialCtx
  namesNodup := by decide
  initialLaw := (FinDist.uniformOfFintype (α := Bool)).map initialState
  obligations := {0, 1}
  program := sourceProgram
  accounts := rfl

def sourceAdmission : CommitmentInterface sourceSetup.program :=
  CommitmentInterface.forfeiture sourceProgram

abbrev nativeGraph := sourceSetup.eventGraph
abbrev bobPublication : nativeGraph.EventId := ⟨0, by decide⟩
abbrev alicePublication : nativeGraph.EventId := ⟨1, by decide⟩

structure Results where
  alice : PublicationResult Bool
  bob : PublicationResult Bool
  deriving DecidableEq

def sourceResults (state : State simpleExpr sourceProgram.terminalCtx) : Results where
  alice := state.get .here
  bob := state.get (.there .here)

def correctness : PublicationResult Bool → PublicationResult Bool → ℝ
  | .success value, guess => if value = guess.isSuccess then 1 else 0
  | .failure, _ => 0

def openingPenalty : PublicationResult Bool → ℝ
  | .success _ => 0
  | .failure => 4

def utility (result : Results) (who : Player) : ℝ :=
  if who = alice then correctness result.alice result.bob - openingPenalty result.alice
  else if who = bob then correctness result.alice result.bob else 0

theorem payoffExpr_eq_utility (env : PlainEnv PayoffCtx) (who : Player) :
    (evalExpr (payoffExpr who) env : ℝ) =
      utility ⟨env.get .here, env.get (.there .here)⟩ who := by
  generalize ha : env.get .here = a
  generalize hb : env.get (.there .here) = b
  fin_cases who <;>
    simp [payoffExpr, alice, bob, utility, correctnessExpr, evalExpr, ha, hb]
  all_goals cases a <;> cases b
  all_goals simp_all [correctness, openingPenalty, PublicationResult.isSuccess,
    PublicationResult.isFailure, PublicationResult.getD]

theorem source_settlement_eq_utility (state : State simpleExpr sourceProgram.terminalCtx) :
    (sourceProgram.evaluatePayoffs state).map (fun payoff => (payoff.1, (payoff.2 : ℝ))) =
      [(alice, utility (sourceResults state) alice),
        (bob, utility (sourceResults state) bob),
        (watcher, utility (sourceResults state) watcher)] := by
  change [(alice, (evalExpr (payoffExpr alice) (sourcePublicEnv state) : ℝ)),
    (bob, (evalExpr (payoffExpr bob) (sourcePublicEnv state) : ℝ)),
    (watcher, (evalExpr (payoffExpr watcher) (sourcePublicEnv state) : ℝ))] = _
  rw [payoffExpr_eq_utility, payoffExpr_eq_utility, payoffExpr_eq_utility]
  rfl

@[simp] theorem utility_alice (result : Results) :
    utility result alice = correctness result.alice result.bob -
      openingPenalty result.alice := rfl

@[simp] theorem utility_bob (result : Results) :
    utility result bob = correctness result.alice result.bob := rfl

@[simp] theorem utility_watcher (result : Results) : utility result watcher = 0 := rfl

end VegasTests.MonitoredGuessing
