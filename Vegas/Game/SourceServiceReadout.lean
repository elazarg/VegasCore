/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Vegas.Compile.EventGraphReadoutComplete
import Interaction.ReactiveNormalHistory

/-! # Typed source readout and base utility of reactive execution

Terminal readout decodes the actual typed store, preserving initial private
cells and public results together. It applies to every scheduler and reads no
watcher record, service calendar, or punishment decision. Base utility uses
that same readout before terminal audit settlement.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Decode the existing typed terminal store, retaining initial private cells
jointly with the public results. An unfinished execution has no readout. -/
def sourceReadout (state : (application setup leaks).ProtocolState) :
    Option (State L setup.program.terminalCtx) :=
  state.bind fun control =>
    let config := control.execution.application.config
    if config.cut.Terminal then
      Vegas.decodeState? (Vegas.terminalRefs setup.program) config.store
    else none

theorem sourceReadout_normalization (state : (application setup leaks).ProtocolState) :
    sourceReadout setup leaks (((runtime setup).reactiveNormalization leaks).state state) =
      sourceReadout setup leaks state := by
  cases state <;> rfl

theorem sourceReadout_eq_some (control : (application setup leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal)
    (source : State L setup.program.terminalCtx)
    (agree : (Vegas.terminalRefs setup.program).Agrees source
      control.execution.application.config.store) :
    sourceReadout setup leaks (some control) = some source := by
  unfold sourceReadout
  rw [Option.bind_some, ite_eq_left terminal]
  exact Vegas.decodeState?_eq_some _ source _ agree

/-- Analysis utility of the actual terminal source readout, prior to a deposit
deduction. Initial private types may affect this utility. -/
def baseUtility (utility : State L setup.program.terminalCtx → Player → ℝ)
    (state : (application setup leaks).ProtocolState) (who : Player) : ℝ :=
  (sourceReadout setup leaks state).elim 0 (fun source => utility source who)

theorem baseUtility_normalization (utility : State L setup.program.terminalCtx → Player → ℝ)
    (state : (application setup leaks).ProtocolState) :
    baseUtility setup leaks utility (((runtime setup).reactiveNormalization leaks).state state) =
      baseUtility setup leaks utility state := by
  unfold baseUtility
  rw [sourceReadout_normalization]

theorem baseUtility_watcher (utility : State L setup.program.terminalCtx → Player → ℝ)
    (watcher : Player) (indifferent : ∀ source, utility source watcher = 0)
    (state : (application setup leaks).ProtocolState) :
    baseUtility setup leaks utility state watcher = 0 := by
  unfold baseUtility
  cases sourceReadout setup leaks state <;>
    simp only [Option.elim_none, Option.elim_some, indifferent]

/-- The compiler's terminal context contains every event output. Consequently
the explicit terminal-cut guard is redundant with successful typed decoding,
even at an arbitrary structurally valid native control state. -/
theorem sourceReadout_eq_decode (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (control : (application setup leaks).Control) :
    sourceReadout setup leaks (some control) =
      decodeState? (terminalRefs setup.program) control.execution.application.config.store := by
  unfold sourceReadout
  rw [Option.bind_some]
  cases decoded : decodeState? (terminalRefs setup.program)
      control.execution.application.config.store with
  | none => simp only [decoded, ite_self]
  | some source =>
      have complete := terminal_decode_complete setup.program .sequential
        control.execution.application.config (by rw [decoded]; rfl)
      dsimp only
      rw [ite_eq_left complete, decoded]

end Vegas
