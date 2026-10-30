/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Compile.EventGraphReadoutComplete
import Vegas.EventGraph.SequentialLaw

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

/-- Read the complete source configuration from the native terminal store and
actual completion history. An unfinished execution has no readout. -/
def serviceSourceReadout (state : (serviceApplication setup mode deadline leaks).ProtocolState) :
    Option (Config Player L setup.program.terminalCtx) :=
  state.bind fun control =>
    let config := control.execution.application.config
    if config.cut.Terminal then
      Vegas.decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        (config.history.map (setup.eventGraph.fromModeCompletion mode))
    else none

/-- Successful full decoding already certifies that every source event is
complete. The explicit terminal guard adds no further readout condition. -/
theorem serviceSourceReadout_eq_decode
    (control : (serviceApplication setup mode deadline leaks).Control) :
    serviceSourceReadout setup mode deadline leaks (some control) =
      decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program)
        control.execution.application.config.store
        (control.execution.application.config.history.map
          (setup.eventGraph.fromModeCompletion mode)) := by
  unfold serviceSourceReadout
  rw [Option.bind_some]
  change (if control.execution.application.config.cut.Terminal then
      (decodeState? (terminalRefs setup.program) control.execution.application.config.store).map _
      else none) =
    (decodeState? (terminalRefs setup.program) control.execution.application.config.store).map _
  cases decoded : decodeState? (terminalRefs setup.program)
      control.execution.application.config.store with
  | none => simp only [Option.map_none, ite_self]
  | some source =>
      have complete := terminal_decode_complete setup.program mode
        control.execution.application.config (by rw [decoded]; rfl)
      rw [ite_eq_left complete]

/-- The complete source readout retains precisely the native public default
history, in every dependency mode. -/
theorem serviceSourceReadout_defaults
    (control : (serviceApplication setup mode deadline leaks).Control)
    (source : Config Player L setup.program.terminalCtx)
    (read : serviceSourceReadout setup mode deadline leaks (some control) = some source) :
    source.defaults = control.execution.application.config.defaults := by
  rw [serviceSourceReadout_eq_decode, decodeConfig?] at read
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp read
  simp only [EventGraph.Config.defaults, EventGraph.Completion.defaults, List.map_map]
  rfl

/-- Every complete native cut has a full source readout, without an execution
provenance or service premise. -/
theorem serviceSourceReadout_exists_of_terminal
    (control : (serviceApplication setup mode deadline leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal) :
    ∃ source, serviceSourceReadout setup mode deadline leaks (some control) = some source := by
  obtain ⟨source, decoded, _⟩ := exists_decodeState_agrees (terminalRefs setup.program)
    control.execution.application.config.store
    (control.execution.application.config.store_available_of_terminal terminal)
  rw [serviceSourceReadout_eq_decode]
  change ∃ final, (decodeState? (terminalRefs setup.program)
    control.execution.application.config.store).map _ = some final
  rw [decoded]
  exact ⟨_, rfl⟩

/-- Analysis utility of the actual terminal source readout, prior to a deposit
deduction. Initial private types may affect this utility. -/
def serviceBaseUtility (utility : Config Player L setup.program.terminalCtx → Player → ℝ)
    (state : (serviceApplication setup mode deadline leaks).ProtocolState) (who : Player) : ℝ :=
  (serviceSourceReadout setup mode deadline leaks state).elim 0 (fun source => utility source who)

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The terminal readout of the supplied runtime. -/
abbrev sourceReadout : (application setup runtime leaks).ProtocolState →
    Option (Config Player L setup.program.terminalCtx) :=
  serviceSourceReadout setup .sequential runtime.deadline leaks

/-- The base utility of the supplied runtime. -/
abbrev baseUtility : (Config Player L setup.program.terminalCtx → Player → ℝ) →
    (application setup runtime leaks).ProtocolState → Player → ℝ :=
  serviceBaseUtility setup .sequential runtime.deadline leaks

end Vegas
