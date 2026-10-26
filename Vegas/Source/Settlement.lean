/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Setup
import GameTheoryExtensions.Math.Transfers

/-! # Integer cash with program-declared exit settlement

An actually excluded owner receives the setup's declared exit transfer, which
replaces every ordinary terminal payment instruction for that owner. Other
owners receive their aggregated executable terminal instructions. An absent
terminal state contributes zero ordinary cash, without suppressing an exit.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Settlement uses actual exclusion, independently of latent source failure. -/
def cash (setup : Setup (Player := Player) (L := L)) (excluded : Finset Player)
    (terminal : Option (State L setup.program.terminalCtx)) (who : Player) : Int :=
  if who ∈ excluded then setup.exitTransfers who else
    terminal.elim 0 (fun state => transferAmount (setup.program.evaluatePayoffs state) who)

@[simp] theorem cash_of_excluded (setup : Setup (Player := Player) (L := L))
    (excluded : Finset Player) (terminal : Option (State L setup.program.terminalCtx))
    (who : Player) (exited : who ∈ excluded) :
    setup.cash excluded terminal who = setup.exitTransfers who := by
  simp only [cash, ite_eq_left exited]

@[simp] theorem cash_of_not_excluded (setup : Setup (Player := Player) (L := L))
    (excluded : Finset Player) (terminal : Option (State L setup.program.terminalCtx))
    (who : Player) (active : who ∉ excluded) :
    setup.cash excluded terminal who =
      terminal.elim 0 (fun state => transferAmount (setup.program.evaluatePayoffs state) who) := by
  simp only [cash, ite_eq_right active]

end Vegas.SourceProgram.Setup
