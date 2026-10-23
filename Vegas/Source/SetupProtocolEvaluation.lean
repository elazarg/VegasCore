/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocol

/-! # Source protocol laws across private setup

At the initial chance position the law integrates over setup. After the draw
it evaluates the retained configuration. The theorem preserves the complete
terminal store, hence every joint reading of persistent types and public data.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def continuationLaw (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    setup.ProtocolState → PMF (State L setup.program.terminalCtx)
  | none => setup.run profile
  | some state => SourceProgram.ProtocolState.continuationLaw setup.program profile state

/-- A finitely branching profile has a finitely supported continuation at every
setup protocol state, the initial draw included when it is finitely supported. -/
theorem continuationLaw_support_finite (setup : Setup (Player := Player) (L := L))
    [setup.FiniteInitialLaw] (profile : BehavioralProfile setup.program)
    (finite : BehavioralProfile.FiniteSupport setup.program profile) :
    (state : setup.ProtocolState) → (setup.continuationLaw profile state).support.Finite
  | none => setup.run_support_finite profile finite
  | some state => SourceProgram.ProtocolState.continuationLaw_support_finite _ profile finite state

def protocolReadout (setup : Setup (Player := Player) (L := L))
    (state : setup.ProtocolState) : Option (State L setup.program.terminalCtx) :=
  state.bind (SourceProgram.ProtocolState.readout setup.program)

theorem continuationLaw_terminal (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (state : setup.ProtocolState)
    (stopped : state.elim False (SourceProgram.ProtocolState.terminal setup.program)) :
    (setup.continuationLaw profile state).map some =
      PMF.pure (setup.protocolReadout state) := by
  cases state with
  | none => exact stopped.elim
  | some state =>
      exact SourceProgram.ProtocolState.continuationLaw_terminal setup.program profile state stopped

end Vegas.SourceProgram.Setup
