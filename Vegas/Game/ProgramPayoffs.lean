/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphCanonical
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
  program.terminalPayoffs.map fun entry => (entry.1, L.toInt (L.eval entry.2 outcome))

@[simp] theorem publicPayoffs_publicOutcome (program : SourceProgram Player L Γ O)
    (state : State L program.terminalCtx) :
    program.publicPayoffs (program.publicOutcome state) = program.evaluatePayoffs state := rfl

/-- Monetary receipts are the sum of every instruction for the player. -/
def publicTransfers (program : SourceProgram Player L Γ O) (outcome : PublicOutcome program)
    (who : Player) : ℝ :=
  transferAmount (program.publicPayoffs outcome) who

/-- Quasi-linear utility with the transfer fixed by the source program. -/
def paymentUtility (program : SourceProgram Player L Γ O)
    (valuation : PublicOutcome program → Player → ℝ) (outcome : PublicOutcome program)
    (who : Player) : ℝ :=
  monetaryUtility valuation (outcome, program.publicTransfers outcome) who

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
        (fun terminal who => (transferAmount (program.evaluatePayoffs terminal) who : ℝ)) := by
      simpa only [PMF.map_comp, Function.comp_def] using law
    _ = _ := by
      congr 1

end Vegas.SourceProgram
