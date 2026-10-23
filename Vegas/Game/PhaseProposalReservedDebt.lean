/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSavedDebt
import Vegas.Pending.ReservedEpochCompletion
import Interaction.ReactiveHistory
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Actual reserved-service continuation payoff of checkpointed own debt -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

local notation "app" => phaseApplication runtime leaks

/-- The same saved-debt conclusion holds for every legal response menu and
arbitrary behavioral continuation at a genuine history. -/
theorem reserved_checkpointDebt_behavioral_terminal_payoff {length : Nat}
    (prior : PMF (ReservedEpoch.Tape Player length))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (menu : (app).ResponseMenu)
    (certificate : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime)
        prior).scheduler).WellFoundedHistories)
    (players : ∀ owner, (menu.information (inputs.map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime)
        prior).scheduler).BehavioralPolicy owner)
    (history final : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime)
        prior).scheduler).History)
    (control : (app).Control) (current : history.state = some control)
    (who : Player) (owed : PhaseCheckpointDebt setup mode plan who control.execution.application)
    (supported : final ∈ ((menu.information (inputs.map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime)
        prior).scheduler).runBehavioralTerminalFrom certificate players history).support)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who =
      excludedPayoff who := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := (ReservedEpoch.implementation runtime leaks
    (ReservedEpoch.packetCapacity runtime) prior).scheduler
  let model := menu.information initial horizon scheduler
  let closed : (app).ProtocolState → Prop := fun state =>
    ∃ control : (app).Control, state = some control ∧
      PhaseCheckpointDebt setup mode plan who control.execution.application
  have retained := model.runBehavioralTerminalFrom_support_closed certificate players closed
    (fun before joint _ after valid reached => by
      obtain ⟨before, rfl, debt⟩ := valid
      obtain ⟨after, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler
        before after joint reached
      exact ⟨after, rfl, phaseCheckpointDebt_transition setup mode runtime leaks plan maximal
        initial horizon scheduler before after joint who debt reached⟩)
    history ⟨control, current, owed⟩ final supported
  obtain ⟨after, state, debt⟩ := retained
  have stopped := model.runBehavioralTerminalFrom_support_terminal certificate players history
    final supported
  have raw := menu.toRawTrace initial horizon scheduler (state ▸ final.trace)
  have exhausted := (ReservedEpoch.implementation_terminal_history_complete runtime leaks
    prior plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs after raw
      (state ▸ stopped)).1
  rw [state]
  exact phaseExclusionBase_of_excluded setup mode runtime leaks utility excludedPayoff after who
    (phaseCheckpointDebt_excluded_of_finished setup mode runtime leaks plan inputs horizon
      scheduler after raw exhausted who debt)

end Vegas
