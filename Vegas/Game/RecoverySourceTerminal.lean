/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCheckpointHistory
import Vegas.Game.RecoverySourceReadout
import Vegas.Game.PhaseExclusionPayoff
import Vegas.Game.CommitRecoveryPayoff
import Vegas.Pending.PhaseTerminalExclusion

/-! # Actual source terminal histories represented by completed phase checkpoints

The surviving typed readout and the entire exclusion-payoff vector agree at a
completed physical endpoint. Every initialized physical history derives its
reachable source checkpoint.
These pointwise results do not assert an information or probability transport.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Exhausting the actual installed plan leaves no source instruction after
the saved semantic checkpoint. -/
theorem RecoverySourceCheckpoint.terminal
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) (finished : state.phases = []) :
    ProtocolState.terminal setup.program
      (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) := by
  apply (ProtocolState.remaining_zero_iff_terminal _ _).mp
  rw [checkpoint.remaining, ProtocolState.remaining_entry]
  rw [← eventCount_eq_instructionCount]
  have bounded := checkpoint.compiled.countEq
  have offset : state.attempt.phase = eventCount setup.program := by
    simp only [PhaseRuntimeState.attempt, finished, List.head?_nil, Option.map_none,
      Option.getD_none]
    rfl
  rw [offset] at bounded
  omega

/-- At an actual finished physical history, the represented source trace has
the same typed readout and the same whole payoff vector. Exclusion equality and
the surviving-store agreement are derived from the actual raw history. -/
theorem RecoverySourceCheckpoint.terminal_history
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (finished : control.execution.application.phases = [])
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    ∃ history : setup.commitRecoveryProtocol.History,
      history.state = some (CommitRecoveryState.atPoint
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
        control.execution.application.entry.excluded control.execution.application.generation) ∧
      setup.commitRecoveryProtocol.terminal history.state ∧
      phaseSourceReadout setup mode runtime leaks (some control) =
        setup.protocolReadout (setup.commitRecoverySourceState history.state) ∧
      (fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
        (some control) who) = fun who => setup.commitRecoveryPayoff utility excludedPayoff who
          history := by
  let history : setup.commitRecoveryProtocol.History := ⟨_, checkpoint.trace⟩
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler trace
  have frontier := (phaseApplication_frontier runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_frontier plan draw) trace
  have complete := frontier.terminal finished
  have flags := phaseTerminalExclusion_history runtime leaks plan inputs horizon scheduler
    trace finished
  have readout : phaseSourceReadout setup mode runtime leaks (some control) =
      setup.protocolReadout (setup.commitRecoverySourceState history.state) := by
    change (if control.execution.application.current.native.config.cut.Terminal then
      decodeState? (terminalRefs setup.program)
        control.execution.application.current.native.config.store else none) = _
    rw [ite_eq_left complete]
    exact checkpoint.terminal_readback finished stored
  refine ⟨history, rfl, checkpoint.terminal finished, readout, ?_⟩
  funext who
  change (if who ∈ control.execution.application.current.excluded then excludedPayoff who else
    (phaseSourceReadout setup mode runtime leaks (some control)).elim 0
      (fun terminal => utility terminal who)) =
    if who ∈ control.execution.application.entry.excluded then excludedPayoff who else
      (setup.protocolReadout (setup.commitRecoverySourceState history.state)).elim 0
        (fun terminal => utility terminal who)
  rw [flags, readout]

end Vegas
