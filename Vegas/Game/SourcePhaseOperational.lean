/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySourceTerminal
import Vegas.Game.PhaseProposalHistory
import Vegas.Game.SourcePhaseGame
import Vegas.Game.PhaseCash
import Vegas.Pending.PhaseLive
import Vegas.Pending.PhaseServiceContract

/-! # Actual completed phase executions have source recovery histories

Maximal physical phases use the existing source exit/retry kernel. Every actual
raw history derives a legal saved source history; completion aligns its actual
excluded set, typed terminal readout and declared integer cash. Counted histories
also retain the full consumed proposal archive. This is pointwise operational
correspondence, without an information, strategy or probability-law assertion.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)

omit [Fintype Player] in
private theorem sourcePhase_terminal_at_checkpoint
    (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (complete : control.execution.application.current.native.config.cut.Terminal) :
    let history : setup.commitRecoveryProtocol.History := ⟨_, checkpoint.trace⟩
    setup.commitRecoveryProtocol.terminal history.state ∧
      history.state.elim ∅ (·.excluded) = control.execution.application.current.excluded ∧
      phaseSourceReadout setup mode runtime leaks (some control) =
        history.state.bind (fun current => ProtocolState.readout setup.program current.point) ∧
      phaseCash setup mode runtime leaks (some control) = setup.sourcePhaseCash history := by
  intro history
  have live := (phaseApplication_live runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨draw, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact ⟨PhaseRuntimeState.initial_frontier plan _, PhaseRuntimeState.initial_live plan _⟩)
    trace
  have finished : control.execution.application.phases = [] := by
    cases phases : control.execution.application.phases with
    | nil => rfl
    | cons phase remaining =>
      have unfinished := live.2 phase (by simp only [phases, List.head?_cons, Option.mem_some_iff])
      apply False.elim
      apply unfinished
      intro event _inside
      rw [complete]
      exact Finset.mem_univ event
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have priorEq : initial = inputs.map (PhaseRuntimeState.initial plan) := by
    rw [PMF.map_comp]
    rfl
  have rawTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control) := by
    rw [← priorEq]
    exact trace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler rawTrace
  have exclusions := phaseTerminalExclusion_history runtime leaks plan inputs horizon scheduler
    rawTrace finished
  have readout : phaseSourceReadout setup mode runtime leaks (some control) =
      history.state.bind (fun current => ProtocolState.readout setup.program current.point) := by
    change (if control.execution.application.current.native.config.cut.Terminal then
      decodeState? (terminalRefs setup.program)
        control.execution.application.current.native.config.store else none) = _
    rw [ite_eq_left complete]
    exact checkpoint.terminal_readback finished stored
  refine ⟨checkpoint.terminal finished, exclusions, readout, ?_⟩
  funext who
  rw [phaseCash_eq_source]
  change setup.cash control.execution.application.current.excluded
      (phaseSourceReadout setup mode runtime leaks (some control)) who =
    setup.cash control.execution.application.entry.excluded
      (history.state.bind (fun current => ProtocolState.readout setup.program current.point)) who
  rw [← exclusions, readout]

/-- Every actual completed raw phase prefix has a genuine source recovery
history, preserving the original observed attempt archive and exact cash vector.
No source history, honesty, policy law or counterpart is supplied by the caller. -/
theorem sourcePhase_terminal_of_raw_trace
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (complete : control.execution.application.current.native.config.cut.Terminal) :
    ∃ checkpoint : RecoverySourceCheckpoint setup mode control.execution.application,
      checkpoint.ArchivedRecall ∧ checkpoint.PublicChronology plan ∧
      ArchivedSourceOrigins setup mode control.execution.application.retired
        ⟨_, checkpoint.trace⟩ ∧
      let history : setup.commitRecoveryProtocol.History := ⟨_, checkpoint.trace⟩
      setup.commitRecoveryProtocol.terminal history.state ∧
        history.state.elim ∅ (·.excluded) = control.execution.application.current.excluded ∧
        phaseSourceReadout setup mode runtime leaks (some control) =
          history.state.bind (fun current => ProtocolState.readout setup.program current.point) ∧
        phaseCash setup mode runtime leaks (some control) = setup.sourcePhaseCash history := by
  obtain ⟨checkpoint, remembered, chronology, origins⟩ := recoverySourceCheckpoint_history
    setup mode runtime leaks plan maximal horizon scheduler trace
  exact ⟨checkpoint, remembered, chronology, origins,
    sourcePhase_terminal_at_checkpoint setup mode runtime leaks plan horizon scheduler
      control trace checkpoint complete⟩

/-- At every actual terminal counted execution, physical completion supplies
one legal terminal source history and the same consumed proposal archive. The
service condition applies to every raw history, including all prior deviations. -/
theorem sourcePhase_terminal_of_counted_trace
    (bounds : MessageBounds (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (completes : PhaseService.CompletesPlay runtime leaks initial horizon scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some control)) (settled : (app).terminal (some control)) :
    ∃ witness : RecoverySourceWitness setup mode plan control.execution.application,
      witness.checkpoint.ArchivedProposals control.execution.network.inputs ∧
      let history : setup.commitRecoveryProtocol.History := ⟨_, witness.checkpoint.trace⟩
      setup.commitRecoveryProtocol.terminal history.state ∧
        history.state.elim ∅ (·.excluded) = control.execution.application.current.excluded ∧
        phaseSourceReadout setup mode runtime leaks (some control) =
          history.state.bind (fun current => ProtocolState.readout setup.program current.point) ∧
        phaseCash setup mode runtime leaks (some control) = setup.sourcePhaseCash history := by
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler trace
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
    trace
  exact ⟨witness, archived,
    sourcePhase_terminal_at_checkpoint setup mode runtime leaks plan horizon scheduler control raw
      witness.checkpoint (completes control raw settled)⟩

end Vegas
