/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphCanonical
import Vegas.Source.InitialState
import GameTheoryExtensions.Analysis.QuasilinearSettlement

/-! # Strategic utility from executable source payments

The program determines monetary transfers by evaluating its terminal payment
expressions on the public outcome. Private valuations are separate data. The
compiled payment reader retains the same realized transfer vector.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

/-- Evaluate the program's payment instructions on their exact public context. -/
def publicPayoffs (program : SourceProgram Player L Γ O) (outcome : PublicOutcome program) :
    List (Player × Int) :=
  program.terminalPayoffs.map fun entry => (entry.1, L.toInt (L.eval entry.2 outcome.values))

@[simp] theorem publicPayoffs_publicOutcome (program : SourceProgram Player L Γ O)
    (state : Config Player L program.terminalCtx) :
    program.publicPayoffs (program.publicOutcome state) = program.evaluatePayoffs state.state := rfl

/-- Monetary receipts are the sum of every instruction for the player. -/
def publicTransfers (program : SourceProgram Player L Γ O) (outcome : PublicOutcome program)
    (who : Player) : ℝ :=
  transferAmount (program.publicPayoffs outcome) who

/-- Quasi-linear utility with the transfer fixed by the source program. -/
def paymentUtility (program : SourceProgram Player L Γ O)
    (valuation : PublicOutcome program → Player → ℝ) (outcome : PublicOutcome program)
    (who : Player) : ℝ :=
  monetaryUtility valuation (outcome, program.publicTransfers outcome) who

@[simp] theorem paymentUtility_eq (program : SourceProgram Player L Γ O)
    (valuation : PublicOutcome program → Player → ℝ) (outcome : PublicOutcome program)
    (who : Player) :
    program.paymentUtility valuation outcome who =
      valuation outcome who + program.publicTransfers outcome who := rfl

/-- Initial parameters may affect valuation, while the executable program alone
determines the monetary receipt from the public result. -/
def parameterPaymentUtility {Parameter : Type} (program : SourceProgram Player L Γ O)
    (valuation : Parameter × PublicOutcome program → Player → ℝ)
    (outcome : Parameter × PublicOutcome program) (who : Player) : ℝ :=
  valuation outcome who + program.publicTransfers outcome.2 who

@[simp] theorem parameterPaymentUtility_eq {Parameter : Type}
    (program : SourceProgram Player L Γ O)
    (valuation : Parameter × PublicOutcome program → Player → ℝ)
    (outcome : Parameter × PublicOutcome program) (who : Player) :
    program.parameterPaymentUtility valuation outcome who =
      valuation outcome who + program.publicTransfers outcome.2 who := rfl

/-- Reading a private initial parameter from the terminal state leaves the
monetary component equal to evaluation of the program's payment instructions. -/
@[simp] theorem Setup.parameterPaymentUtility_parameterOutcome {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (terminal : Config Player L setup.program.terminalCtx) (who : Player) :
    setup.program.parameterPaymentUtility valuation
        (setup.parameterOutcome parameter terminal) who =
      valuation (setup.parameterOutcome parameter terminal) who +
        (transferAmount (setup.program.evaluatePayoffs terminal.state) who : ℝ) := rfl

/-- Canonical compilation preserves each player's aggregated monetary receipt,
not merely the syntax of the payment instruction list. -/
theorem canonical_transfer_law (program : SourceProgram Player L Γ O)
    (profile : BehavioralProfile program) (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes (toEventGraph program).canonicalScheduler
        (compileEventProfile program profile) (encodeInputs state)).map
        (fun terminal who => (transferAmount (terminalPayouts program terminal) who : ℝ)) =
      (program.run profile state).map
        (fun terminal => program.publicTransfers (program.publicOutcome terminal)) := by
  have law := congrArg
    (fun distribution : PMF (List (Player × Int)) => distribution.map
      (fun entries who => (transferAmount entries who : ℝ)))
    (Vegas.canonical_payout_law program profile state)
  calc
    _ = (program.run profile state).map
        (fun terminal who =>
          (transferAmount (program.evaluatePayoffs terminal.state) who : ℝ)) := by
      simpa only [PMF.map_comp, Function.comp_def] using law
    _ = _ := by
      congr 1

end Vegas.SourceProgram
