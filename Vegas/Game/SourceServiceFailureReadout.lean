/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Compile.EventGraphReadoutComplete
import Vegas.Game.RevealServiceRosterContinuation

/-! # Decoded failures in existing terminal source readouts -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {profile : BehavioralProfile setup.program}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A decoded owed failure appears in every existing terminal source readout. -/
theorem decoded_owesFailure_failedReveals_of_readout
    (who : Player) (state : (application setup leaks).ProtocolState)
    (owed : DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program) state)
    (terminal : State L setup.program.terminalCtx)
    (readout : sourceReadout setup leaks state = some terminal) :
    1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  cases state with
  | none => exact owed.elim
  | some control =>
      obtain ⟨rank, ⟨residual⟩, decoded⟩ := owed
      rw [sourceReadout_eq_decode] at readout
      have complete := terminal_decode_complete setup.program .sequential
        control.execution.application.config (by rw [readout]; rfl)
      have full := isPrefix_eventCount_of_terminal residual.checkpoint.ordered complete
      subst full
      have read := sourceServicePrefix?_terminal_readout setup control.execution.application.config
      have decodeAtEnd : sourceServicePrefix? setup (eventCount setup.program)
          control.execution.application.config =
            some (residual.lift (ProtocolState.entry residual.program residual.source)) :=
        residual.decode
      rw [decodeAtEnd] at read
      have pointRead : ProtocolState.readout setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source)) =
            some terminal := read.trans readout
      exact ProtocolState.failedReveals_pos_of_owesFailure who setup.program _
        (decoded _ residual.decode) pointRead

end Vegas
