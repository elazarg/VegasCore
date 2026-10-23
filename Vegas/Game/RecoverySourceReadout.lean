/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Pending.PhaseStoredCheckpoint

/-! # Current terminal readout from reachable saved source checkpoints -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The live semantic store retains every typed cell represented at the saved
source checkpoint, even when its current concurrent cut has holes. -/
theorem RecoverySourceCheckpoint.current_agrees
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) (stored : state.StoredCheckpoint) :
    checkpoint.refs.Agrees checkpoint.source.state state.current.native.config.store := by
  intro name cell selected
  exact (checkpoint.refs.get selected).get?_preserved _ _ stored _ (checkpoint.agrees selected)


private theorem terminal_readback_of_zero
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (program : SourceProgram Player L Γ O)
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (aligned : CompiledReadoutSuffix whole program refs embedding)
    (source : SourceProgram.Config Player L Γ) (store : Store (graphLayout whole))
    (agrees : refs.Agrees source.state store) (empty : eventCount program = 0) :
    decodeState? (terminalRefs whole) store =
      (ProtocolState.readout program (ProtocolState.entry program source)).map
        (cast (congrArg (State L) aligned.contextEq)) := by
  cases program with
  | ret payoffs => exact aligned.decode_ret whole payoffs refs embedding source.state store agrees
  | sample => simp only [eventCount] at empty; omega
  | commit => simp only [eventCount] at empty; omega
  | reveal => simp only [eventCount] at empty; omega

/-- Once the installed physical plan is exhausted, its saved typed checkpoint
determines the actual current canonical terminal readout. No decoder registry
equality or source-order condition on intermediate concurrent cuts is used. -/
theorem RecoverySourceCheckpoint.terminal_readback
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) (finished : state.phases = [])
    (stored : state.StoredCheckpoint) :
    decodeState? (terminalRefs setup.program) state.current.native.config.store =
      ProtocolState.readout setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) := by
  rw [checkpoint.readout]
  apply terminal_readback_of_zero setup.program checkpoint.residual.tail checkpoint.refs
    checkpoint.embedding checkpoint.terminalAlignment checkpoint.source
    state.current.native.config.store (checkpoint.current_agrees stored)
  have bounded := checkpoint.compiled.countEq
  have offset : state.attempt.phase = eventCount setup.program := by
    simp only [PhaseRuntimeState.attempt, finished, List.head?_nil, Option.map_none,
      Option.getD_none]
    rfl
  rw [offset] at bounded
  omega

end Vegas
