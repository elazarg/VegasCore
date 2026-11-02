/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Compile.EventGraphReadoutComplete
import Vegas.Game.RevealServicePayoffs
import Vegas.Game.SourceServiceDecodedDebt
import Vegas.Game.OnePacketForced

/-! # Owed failures in full terminal source readouts -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {profile : BehavioralProfile setup.program}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem decoded_terminal_readout
    (control : (application setup runtime leaks).Control)
    {property : ProtocolState setup.program → Prop}
    (holds : DecodedState setup runtime leaks profile property (some control))
    (terminal : Config Player L setup.program.terminalCtx)
    (readout : sourceReadout setup runtime leaks (some control) = some terminal) :
    ∃ point, control.execution.application.config.cut.IsPrefix (eventCount setup.program) ∧
      sourceServicePrefix? setup (eventCount setup.program)
        control.execution.application.config = some point ∧
      property point ∧ ProtocolState.readout setup.program point = some terminal := by
  obtain ⟨rank, ⟨residual⟩, valid⟩ := holds
  have complete : control.execution.application.config.cut.Terminal := by
    by_contra incomplete
    simp only [sourceReadout, serviceSourceReadout, Option.bind_some, incomplete,
      ite_false] at readout
    cases readout
  have atEnd : control.execution.application.config.cut.IsPrefix
      (eventCount setup.program) := by
    refine ⟨le_rfl, ?_⟩
    intro event
    rw [complete]
    exact iff_of_true (Finset.mem_univ event) event.isLt
  have full := residual.checkpoint.ordered.unique atEnd
  subst rank
  rw [sourceReadout, serviceSourceReadout_eq_decode] at readout
  have read := sourceServicePrefix?_terminal_readout setup control.execution.application.config
  have decoded : sourceServicePrefix? setup (eventCount setup.program)
      control.execution.application.config = some
        (residual.lift (ProtocolState.entry residual.program residual.source)) := residual.decode
  rw [decoded] at read
  exact ⟨_, atEnd, decoded, valid _ residual.decode, read.trans readout⟩

/-- A decoded owed failure appears in every successful terminal source readout. -/
theorem decoded_owesFailure_failedReveals_of_readout
    (who : Player) (state : (application setup runtime leaks).ProtocolState)
    (owed : DecodedState setup runtime leaks profile (ProtocolState.OwesFailure
      who setup.program) state)
    (terminal : Config Player L setup.program.terminalCtx)
    (readout : sourceReadout setup runtime leaks state = some terminal) :
    1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  cases state with
  | none => exact owed.elim
  | some control =>
      obtain ⟨point, _, _, hasDebt, pointRead⟩ := decoded_terminal_readout control owed terminal
        readout
      exact ProtocolState.failedReveals_pos_of_owesFailure who setup.program point hasDebt pointRead

/-- At an initialized native history, an owed failure in a complete readout
publicly defaults its owner. The publication provenance is derived from the history. -/
theorem decoded_owesFailure_defaulted_of_readout
    {menu : (application setup runtime leaks).ResponseMenu} {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup runtime leaks profile (ProtocolState.OwesFailure
      who setup.program) history.state)
    (terminal : Config Player L setup.program.terminalCtx)
    (readout : sourceReadout setup runtime leaks history.state = some terminal) :
    who ∈ terminal.defaulted := by
  cases current : history.state with
  | none => rw [current] at owed; exact owed.elim
  | some control =>
      rw [current] at owed readout
      obtain ⟨point, ordered, decoded, hasDebt, pointRead⟩ :=
        decoded_terminal_readout control owed terminal readout
      exact ProtocolState.defaulted_of_owesFailure_of_publicationsDefaulted who setup.program
        point (publicationsDefaulted_of_decode history control current ordered decoded)
        hasDebt pointRead

/-- A completed native continuation with source debt has the declared exit
utility, using the same public default set as the source readout. -/
theorem decoded_owesFailure_exclusionBase_of_readout {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {menu : (application setup runtime leaks).ResponseMenu} {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup runtime leaks profile (ProtocolState.OwesFailure
      who setup.program) history.state)
    (terminal : Config Player L setup.program.terminalCtx)
    (readout : sourceReadout setup runtime leaks history.state = some terminal) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks history.state who =
      excludedPayoff who := by
  have defaulted := decoded_owesFailure_defaulted_of_readout who history owed terminal readout
  cases current : history.state with
  | none => rw [current] at owed; exact owed.elim
  | some control =>
      rw [current] at readout
      apply exclusionBase_of_defaulted
      change who ∈ control.execution.application.config.defaults.defaulted
      rw [← serviceSourceReadout_defaults setup .sequential runtime.deadline leaks control
        terminal readout]
      exact defaulted

end Vegas
