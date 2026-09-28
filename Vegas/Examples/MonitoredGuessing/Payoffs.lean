/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.Game
import Vegas.EventGraph.PayoffTransport

/-! # A source family with arbitrary declared integer payoffs

The ordinary source program still publishes Bob's Boolean choice and then
Alice's initialized Boolean commitment. Its return expressions may specify any
integer payoff table over both publication results, including failures.
Changing that table preserves the compiled event code and every adaptive event
execution law. This is an operational transport, not an equilibrium theorem:
different tables can change the incentives to open, disclose, or report.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

abbrev PayoffTable := Results → Player → Int

private def resultChoice {Γ : CtxSimple} (result : Expr Γ (.result .bool))
    (failure onFalse onTrue : Expr Γ .int) : Expr Γ .int :=
  .ite (.isSuccess result) (.ite (.getResultD result (.constBool false)) onTrue onFalse)
    failure

def tableExpr (table : PayoffTable) (who : Player) : Expr PayoffCtx .int :=
  let a : Expr PayoffCtx (.result .bool) := .var 3 .here
  let b : Expr PayoffCtx (.result .bool) := .var 2 (.there .here)
  let row := fun result => resultChoice b
    (.constInt (table ⟨result, .failure⟩ who))
    (.constInt (table ⟨result, .success false⟩ who))
    (.constInt (table ⟨result, .success true⟩ who))
  resultChoice a (row .failure) (row (.success false)) (row (.success true))

theorem tableExpr_eval (table : PayoffTable) (who : Player) (env : PlainEnv PayoffCtx) :
    evalExpr (tableExpr table who) env =
      table ⟨env.get .here, env.get (.there .here)⟩ who := by
  generalize first : env.get .here = a
  generalize second : env.get (.there .here) = b
  cases a with
  | failure =>
      cases b with
      | failure => simp [tableExpr, resultChoice, evalExpr, first, second,
          PublicationResult.isSuccess]
      | success value => cases value <;> simp [tableExpr, resultChoice, evalExpr, first, second,
          PublicationResult.isSuccess, PublicationResult.getD]
  | success value =>
      cases value <;> cases b with
      | failure => simp [tableExpr, resultChoice, evalExpr, first, second,
          PublicationResult.isSuccess, PublicationResult.getD]
      | success value => cases value <;> simp [tableExpr, resultChoice, evalExpr, first, second,
          PublicationResult.isSuccess, PublicationResult.getD]

def payoffProgram (table : PayoffTable) :
    SourceProgram Player simpleExpr initialCtx {0, 1} :=
  .reveal 2 bob 1 (by decide) (.there .here) (by decide) <|
  .reveal 3 alice 0 (by decide) (.there .here) (by decide) <|
  .ret [(alice, tableExpr table alice), (bob, tableExpr table bob),
    (watcher, tableExpr table watcher)]

def payoffSetup (table : PayoffTable) : Setup (Player := Player) (L := simpleExpr) where
  context := initialCtx
  namesNodup := by decide
  initialLaw := (FinDist.uniformOfFintype (α := Bool)).map initialState
  obligations := {0, 1}
  program := payoffProgram table
  accounts := rfl

/-- These are the source program's actual declared returns, without an
external reinterpretation of the old correctness-payoff program. -/
theorem payoffProgram_settlement (table : PayoffTable)
    (state : State simpleExpr (payoffProgram table).terminalCtx) :
    (payoffProgram table).evaluatePayoffs state =
      [(alice, table (sourceResults state) alice),
       (bob, table (sourceResults state) bob),
       (watcher, table (sourceResults state) watcher)] := by
  change [(alice, evalExpr (tableExpr table alice) _),
    (bob, evalExpr (tableExpr table bob) _),
    (watcher, evalExpr (tableExpr table watcher) _)] = _
  simp only [tableExpr_eval]
  rfl

def compiledPayoffs (table : PayoffTable) :
    List (Player × EventGraph.PublicExpr nativeGraph.layout simpleExpr.int) := by
  simpa only [Vegas.graphLayout, EventGraph.layout, nativeGraph, sourceSetup,
    Setup.eventGraph, Vegas.toEventGraph, payoffProgram, sourceProgram,
    Vegas.outputLayout, Vegas.eventCount]
      using Vegas.payoffs (payoffProgram table)

/-- The ordinary compiler changes only terminal readout expressions. -/
theorem payoffSetup_graph (table : PayoffTable) :
    (payoffSetup table).eventGraph = nativeGraph.withPayoffs (compiledPayoffs table) := by
  rfl

/-- The initial distribution and its encoded commitment meanings are unchanged. -/
theorem payoffSetup_inputs (table : PayoffTable) (bit : Bool) :
    (payoffSetup table).eventInputs (initialState bit) =
      sourceSetup.eventInputs (initialState bit) := rfl

/-- Every causal event plan, including all of its adaptive actions, has the
same complete store and action-history law under arbitrary declared payoffs. -/
theorem payoffProgram_run (table : PayoffTable) (plan : nativeGraph.EventPlan)
    (inputs : nativeGraph.Inputs) :
    ((payoffSetup table).eventGraph.run inputs
      (nativeGraph.planWithPayoffs (compiledPayoffs table) plan)) =
      (nativeGraph.run inputs plan).map
        (nativeGraph.configWithPayoffs (compiledPayoffs table)) :=
  nativeGraph.run_withPayoffs (compiledPayoffs table) plan inputs

end Vegas.Examples.MonitoredGuessing
