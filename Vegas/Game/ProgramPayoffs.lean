/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphCanonical
import Vegas.Source.InitialState
import GameTheoryExtensions.Analysis.QuasilinearSettlement

/-! # Strategic utility from executable source payments

A program evaluates its terminal payment instructions on the public outcome.
A setup replaces a defaulted player's instruction sum by its declared exit
transfer. Private valuation is separate from both payment rules.
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

/-- Sum the terminal payment instructions before the setup's exit override. -/
def publicTransfers (program : SourceProgram Player L Γ O) (outcome : PublicOutcome program)
    (who : Player) : ℝ :=
  transferAmount (program.publicPayoffs outcome) who

/-- Valuation plus the instruction-payment sum, before any setup exit override. -/
def paymentSumUtility (program : SourceProgram Player L Γ O)
    (valuation : PublicOutcome program → Player → ℝ) (outcome : PublicOutcome program)
    (who : Player) : ℝ :=
  monetaryUtility valuation (outcome, program.publicTransfers outcome) who

@[simp] theorem paymentSumUtility_eq (program : SourceProgram Player L Γ O)
    (valuation : PublicOutcome program → Player → ℝ) (outcome : PublicOutcome program)
    (who : Player) :
    program.paymentSumUtility valuation outcome who =
      valuation outcome who + program.publicTransfers outcome who := rfl

/-- Actual receipts use the declared exit transfer after public default. -/
def Setup.transfers (setup : Setup (Player := Player) (L := L))
    (outcome : PublicOutcome setup.program) (who : Player) : ℝ :=
  if who ∈ outcome.defaults.defaulted then (setup.exitTransfers who : ℝ)
  else setup.program.publicTransfers outcome who

/-- Valuation plus the setup's default-aware executable receipts. -/
def Setup.parameterPaymentUtility {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (outcome : Parameter × PublicOutcome setup.program) (who : Player) : ℝ :=
  valuation outcome who + setup.transfers outcome.2 who

@[simp] theorem Setup.parameterPaymentUtility_eq {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (outcome : Parameter × PublicOutcome setup.program) (who : Player) :
    setup.parameterPaymentUtility valuation outcome who =
      valuation outcome who + setup.transfers outcome.2 who := rfl

/-- Both valuation and receipts use the same full source observation. -/
@[simp] theorem Setup.parameterPaymentUtility_parameterOutcome {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (terminal : Config Player L setup.program.terminalCtx) (who : Player) :
    setup.parameterPaymentUtility valuation (setup.parameterOutcome parameter terminal) who =
      valuation (setup.parameterOutcome parameter terminal) who +
        setup.transfers (setup.program.publicOutcome terminal) who := rfl

/-- Canonical compilation preserves each player's aggregated instruction-payment
sum, before the setup's exit override. -/
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
