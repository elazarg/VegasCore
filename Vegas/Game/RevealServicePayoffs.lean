/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Compile.EventGraphReadout

/-! # Net utilities for the monitored reveal service

One collectible deposit per ordinary player is charged at settlement when a
packet it signed, on the ledger or in the watcher's report, is forbidden by the
settled record. The utility and deposit are fixed before choosing an
equilibrium. Reporting has no separate payment here; the watcher retains its
declared base utility and must be indifferent for the watcher-extension theorem.

The comparison tolerates arbitrary outcomes after an extra response, including
communication that a recipient reads before the watcher reports. Its probability
bound concerns actual collection evidence, supplied by the monitored service.
The deduction models collection in utility units, not an implementation of escrow.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Decode the existing typed terminal store, retaining initial private cells
jointly with the public results. An unfinished execution has no readout. -/
def serviceSourceReadout (state : (serviceApplication setup mode deadline leaks).ProtocolState) :
    Option (State L setup.program.terminalCtx) :=
  state.bind fun control =>
    let config := control.execution.application.config
    if config.cut.Terminal then
      Vegas.decodeState? (Vegas.terminalRefs setup.program) config.store
    else none

/-- Analysis utility of the actual terminal source readout, prior to a deposit
deduction. Initial private types may affect this utility. -/
def serviceBaseUtility (utility : State L setup.program.terminalCtx → Player → ℝ)
    (state : (serviceApplication setup mode deadline leaks).ProtocolState) (who : Player) : ℝ :=
  (serviceSourceReadout setup mode deadline leaks state).elim 0 (fun source => utility source who)

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The terminal readout of the default runtime. -/
abbrev sourceReadout : (application setup leaks).ProtocolState →
    Option (State L setup.program.terminalCtx) :=
  serviceSourceReadout setup .sequential (rankDeadline setup .sequential) leaks

/-- The base utility of the default runtime. -/
abbrev baseUtility : (State L setup.program.terminalCtx → Player → ℝ) →
    (application setup leaks).ProtocolState → Player → ℝ :=
  serviceBaseUtility setup .sequential (rankDeadline setup .sequential) leaks

end Vegas
