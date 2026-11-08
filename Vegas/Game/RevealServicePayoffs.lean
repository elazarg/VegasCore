/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Compile.EventGraphReadoutComplete
import Vegas.EventGraph.SequentialLaw

/-! # Complete source readout and base utility

The service reader decodes the native graph's typed terminal store and history
into a complete source configuration, retaining its public default record.
The base utility evaluates a supplied payoff at that readout and is zero when
no source configuration is available.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Utility of the terminal configuration a reader recovers from a native state,
and zero when the reader recovers none. -/
def readoutBaseUtility {State Terminal : Type} (reader : State → Option Terminal)
    (utility : Terminal → Player → ℝ) (state : State) (who : Player) : ℝ :=
  (reader state).elim 0 (fun source => utility source who)

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (duration : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Read the complete source configuration from the native terminal store and
actual completion history. An unfinished execution has no readout. -/
def serviceSourceReadout (state : (serviceApplication setup mode duration leaks).ProtocolState) :
    Option (Config Player L setup.program.terminalCtx) :=
  state.bind fun control =>
    let config := control.execution.application.config
    if config.cut.Terminal then
      Vegas.decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        config.history
    else none

/-- Successful full decoding already certifies that every source event is
complete. The explicit terminal guard adds no further readout condition. -/
theorem serviceSourceReadout_eq_decode
    (control : (serviceApplication setup mode duration leaks).Control) :
    serviceSourceReadout setup mode duration leaks (some control) =
      decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program)
        control.execution.application.config.store
        control.execution.application.config.history := by
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
    (control : (serviceApplication setup mode duration leaks).Control)
    (source : Config Player L setup.program.terminalCtx)
    (read : serviceSourceReadout setup mode duration leaks (some control) = some source) :
    source.defaults = control.execution.application.config.defaults := by
  rw [serviceSourceReadout_eq_decode, decodeConfig?] at read
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp read
  simp only [EventGraph.Config.defaults, EventCompletion.defaults]
  rfl

/-- Every complete native cut has a full source readout, without an execution
provenance or service premise. -/
theorem serviceSourceReadout_exists_of_terminal
    (control : (serviceApplication setup mode duration leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal) :
    ∃ source, serviceSourceReadout setup mode duration leaks (some control) = some source := by
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
    (state : (serviceApplication setup mode duration leaks).ProtocolState) (who : Player) : ℝ :=
  (serviceSourceReadout setup mode duration leaks state).elim 0 (fun source => utility source who)

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The terminal readout of the supplied runtime. -/
abbrev sourceReadout : (application setup timeouts leaks).ProtocolState →
    Option (Config Player L setup.program.terminalCtx) :=
  serviceSourceReadout setup .sequential timeouts.duration leaks

/-- The base utility of the supplied runtime. -/
abbrev baseUtility : (Config Player L setup.program.terminalCtx → Player → ℝ) →
    (application setup timeouts leaks).ProtocolState → Player → ℝ :=
  serviceBaseUtility setup .sequential timeouts.duration leaks

end Vegas
