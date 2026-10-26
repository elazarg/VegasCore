/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryInformation
import Vegas.Source.Settlement
import GameTheory.Protocol.Strategic
import GameTheory.Core.Utility

/-! # Declared monetary utility of the source phase game

The game uses the existing source recovery protocol, information and evaluator.
Its finite instruction budget includes the private setup draw and every retry.
Actual permanent exclusion selects declared exit cash; ordinary executable
`ret` transfers remain in force for other players. Valuation is independent
analysis data over the complete source history and is never clipped by cash
settlement. A preservation result additionally needs the chosen valuation to
factor through the information retained by its implementation; no such
factorization or runtime equilibrium correspondence is asserted here.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Integer cash is read from the actual source phase exclusion snapshot and
source program point, including exclusion before a terminal readout exists. -/
def sourcePhaseCash (history : setup.commitRecoveryProtocol.History) (who : Player) : Int :=
  setup.cash (history.state.elim ∅ (·.excluded))
    (history.state.bind fun current => ProtocolState.readout setup.program current.point) who

/-- Every behavioral policy uses the existing recovery evaluator. The outcome
retains the entire history, allowing valuation to depend on all its source data. -/
def sourcePhaseGame [Fintype Player]
    (valuation : setup.commitRecoveryProtocol.History → Player → ℝ) : UtilityGame Player where
  form := setup.commitRecoveryModel.toBehavioralGameForm
    ((Fintype.card Player + 1) * (instructionCount setup.program + 1))
  utility history who := valuation history who + (setup.sourcePhaseCash history who : ℝ)

/-- The proved source retry budget completes every profile, without a finite
initial prior, finite local menus or a rationality premise. -/
theorem sourcePhaseGame_terminal [Fintype Player]
    (valuation : setup.commitRecoveryProtocol.History → Player → ℝ)
    (profile : Profile (setup.sourcePhaseGame valuation).form.sig)
    (history : setup.commitRecoveryProtocol.History)
    (supported : history ∈ ((setup.sourcePhaseGame valuation).form.play profile).support) :
    setup.commitRecoveryProtocol.terminal history.state :=
  setup.commitRecoveryModel.runBehavioralFrom_terminal_of_bound profile
    setup.commitRecoveryProtocol_bounded setup.commitRecoveryProtocol.initHistory history supported

/-- An exited player's declared cash overrides the whole ordinary transfer
list, even before source execution has reached a terminal store. -/
theorem sourcePhaseCash_of_excluded
    (history : setup.commitRecoveryProtocol.History) (current : CommitRecoveryState setup.program)
    (atState : history.state = some current) (who : Player) (exited : who ∈ current.excluded) :
    setup.sourcePhaseCash history who = setup.exitTransfers who := by
  simp only [sourcePhaseCash, atState, Option.elim_some, Option.bind_some]
  exact setup.cash_of_excluded _ _ who exited

/-- Without actual exclusion, a complete readout evaluates the original source
program's payment instructions, rather than an independently supplied utility. -/
theorem sourcePhaseCash_of_terminal
    (history : setup.commitRecoveryProtocol.History) (current : CommitRecoveryState setup.program)
    (atState : history.state = some current) (who : Player) (active : who ∉ current.excluded)
    (terminal : State L setup.program.terminalCtx)
    (read : ProtocolState.readout setup.program current.point = some terminal) :
    setup.sourcePhaseCash history who = transferAmount (setup.program.evaluatePayoffs terminal)
      who := by
  simp only [sourcePhaseCash, atState, Option.elim_some, Option.bind_some, read,
    cash_of_not_excluded setup _ _ who active, Option.elim_some]

/-- Exit cash does not overwrite the separately declared history valuation. -/
theorem sourcePhaseGame_utility_of_excluded [Fintype Player]
    (valuation : setup.commitRecoveryProtocol.History → Player → ℝ)
    (history : setup.commitRecoveryProtocol.History) (current : CommitRecoveryState setup.program)
    (atState : history.state = some current) (who : Player) (exited : who ∈ current.excluded) :
    (setup.sourcePhaseGame valuation).utility history who =
      valuation history who + (setup.exitTransfers who : ℝ) := by
  change valuation history who + (setup.sourcePhaseCash history who : ℝ) = _
  rw [setup.sourcePhaseCash_of_excluded history current atState who exited]

/-- Excluded players are not strategic actors of the existing source kernel. -/
theorem sourcePhase_not_active_of_excluded
    (history : setup.commitRecoveryProtocol.History) (current : CommitRecoveryState setup.program)
    (atState : history.state = some current) (who : Player) (exited : who ∈ current.excluded) :
    ¬ setup.commitRecoveryProtocol.active history.state who := by
  rw [atState]
  exact fun active => active.2 exited

/-- At an actual exited information value the entire legal choice space
contains only silence. All future owned source instructions are automatic. -/
theorem sourcePhase_choice_eq_none_of_excluded
    (history : setup.commitRecoveryProtocol.History) (current : CommitRecoveryState setup.program)
    (atState : history.state = some current) (who : Player) (exited : who ∈ current.excluded)
    (choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryModel.infoOf who history.trace)) :
    choice.1 = none := by
  have offered := (setup.commitRecoveryModel.menu_adequate who history.trace choice.1).mp choice.2
  cases selected : choice.1 with
  | none => rfl
  | some move =>
    rw [selected] at offered
    exact (setup.sourcePhase_not_active_of_excluded history current atState who exited
      offered.1).elim

end Vegas.SourceProgram.Setup
