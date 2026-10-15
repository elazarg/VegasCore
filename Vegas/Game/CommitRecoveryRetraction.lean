/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryEmbedding
import Vegas.Source.IntendedTraceUnique

/-! # Retraction of intended histories from clear source recovery histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Project an actual clear recovery history, retaining its effective source
actions and the original private setup draw. -/
def commitRecoveryClearHistory (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state) :
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History :=
  ⟨setup.commitRecoverySourceState history.state,
    setup.commitRecoveryClearTrace history.trace clear⟩

theorem commitRecoveryLiftHistory_injective (wellFormed : setup.WellFormed) :
    Function.Injective (setup.commitRecoveryLiftHistory wellFormed) := by
  intro first second same
  apply setup.intendedProtocol_history_eq_of_state
  have projected := congrArg
    (fun history : setup.commitRecoveryProtocol.History =>
      setup.commitRecoverySourceState history.state) same
  simpa only [commitRecoveryLiftHistory_source] using projected

/-- Lifting and then projecting recovers the complete original source history,
including choices made at histories outside any selected equilibrium support. -/
theorem commitRecoveryClearHistory_lift (wellFormed : setup.WellFormed)
    (original : setup.intendedProtocol.History) :
    setup.commitRecoveryClearHistory (setup.commitRecoveryLiftHistory wellFormed original)
      (setup.commitRecoveryLiftHistory_clear wellFormed original) =
      (setup.intendedRestriction (CommitmentInterface.forfeiture setup.program)).history
        original := by
  have state : (setup.commitRecoveryClearHistory
        (setup.commitRecoveryLiftHistory wellFormed original)
        (setup.commitRecoveryLiftHistory_clear wellFormed original)).state =
      ((setup.intendedRestriction (CommitmentInterface.forfeiture setup.program)).history
        original).state := setup.commitRecoveryLiftHistory_source wellFormed original
  generalize setup.commitRecoveryClearHistory
    (setup.commitRecoveryLiftHistory wellFormed original)
    (setup.commitRecoveryLiftHistory_clear wellFormed original) = first at state ⊢
  generalize (setup.intendedRestriction (CommitmentInterface.forfeiture setup.program)).history
    original = second at state ⊢
  obtain ⟨firstPoint, firstTrace⟩ := first
  obtain ⟨secondPoint, secondTrace⟩ := second
  change firstPoint = secondPoint at state
  subst secondPoint
  have unique := setup.executionProtocol_isTreeShaped
    (CommitmentInterface.forfeiture setup.program) firstPoint
  rw [Subsingleton.elim firstTrace secondTrace]

theorem commitRecoveryLiftHistory_terminal (wellFormed : setup.WellFormed)
    (original : setup.intendedProtocol.History) :
    setup.commitRecoveryProtocol.terminal
        (setup.commitRecoveryLiftHistory wellFormed original).state ↔
      setup.intendedProtocol.terminal original.state := by
  have projected := setup.commitRecoveryLiftHistory_source wellFormed original
  have terminal (state : setup.commitRecoveryProtocol.State) :
      setup.commitRecoveryProtocol.terminal state ↔
        setup.intendedProtocol.terminal (setup.commitRecoverySourceState state) := by
    cases state <;> rfl
  rw [terminal, projected]

theorem commitRecoveryLiftHistory_active (wellFormed : setup.WellFormed)
    (original : setup.intendedProtocol.History) (who : Player) :
    setup.commitRecoveryProtocol.active
        (setup.commitRecoveryLiftHistory wellFormed original).state who ↔
      setup.intendedProtocol.active original.state who := by
  have projected := setup.commitRecoveryLiftHistory_source wellFormed original
  have clear := setup.commitRecoveryLiftHistory_clear wellFormed original
  generalize (setup.commitRecoveryLiftHistory wellFormed original).state = current
    at projected clear ⊢
  rw [← projected]
  cases current with
  | none => rfl
  | some current =>
      change (_ ∧ who ∉ current.excluded) ↔ _
      change current.excluded = ∅ at clear
      rw [clear]
      simp only [Finset.notMem_empty, not_false_eq_true, and_true,
        commitRecoverySourceState, Option.map_some,
        intendedProtocol, restrictAvailable, executionProtocol, Option.elim_some,
        protocolObserve, Option.map_some, ProtocolState.actor_observe_eq]

end Vegas.SourceProgram.Setup
