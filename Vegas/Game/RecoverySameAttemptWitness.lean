/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalInstalledSourceHistory

/-! # The same selected source checkpoint along an unfinished physical attempt -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "graph" => serviceGraph setup mode
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

omit [Fintype Player] in
/-- Transferring the same saved checkpoint leaves both actual binding
readouts unchanged. The proof eliminates only the transfer equalities. -/
theorem RecoverySourceCheckpoint.transfer_binding_readback
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state other : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (entry : other.entry = state.entry) (generation : other.generation = state.generation)
    (offset : other.attempt.phase = state.attempt.phase)
    (image : RecoveryState (serviceGraph setup mode)) :
    (checkpoint.transfer entry generation offset).commitResultPoint image =
        checkpoint.commitResultPoint image ∧
      (checkpoint.transfer entry generation offset).commitInstructionWord image.native =
        checkpoint.commitInstructionWord image.native := by
  rcases state with ⟨phases, currentGeneration, saved, current, retired⟩
  rcases other with ⟨otherPhases, otherGeneration, otherSaved, otherCurrent, otherRetired⟩
  dsimp only at entry generation
  cases entry
  cases generation
  exact ⟨rfl, rfl⟩

/-- The actual prefix retains the supplied checkpoint by explicit transfer
with its full archive. -/
theorem RecoverySourceWitness.prefix_at_same_attempt
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (scheduler : (app).Scheduler) (anchor current : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (currentTrace : ((menu).protocol initial horizon scheduler).Trace (some current))
    (kept : TracePrefix anchorTrace currentTrace)
    (same : current.execution.application.attempt = anchor.execution.application.attempt)
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs) :
    ∃ next : RecoverySourceWitness setup mode plan current.execution.application,
      next.checkpoint.ArchivedProposals current.execution.network.inputs ∧
      (⟨_, next.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
        ⟨_, witness.checkpoint.trace⟩ ∧
      ∃ saved : current.execution.application.entry = anchor.execution.application.entry,
        next.checkpoint = witness.checkpoint.transfer saved
          (congrArg CommitAttemptId.generation same) (congrArg CommitAttemptId.phase same) := by
  have follower := RecoverySourceWitness.prefix_archived_source setup mode runtime leaks bounds
    plan maximal horizon scheduler
  have initialLaw : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  rw [← initialLaw] at follower
  obtain ⟨selected, stateEq, next, nextArchived, fuel, path⟩ :=
    follower anchor anchorTrace witness archived currentTrace kept
  cases Option.some.inj stateEq
  have firstPosition := witness.checkpoint.saved_position
  have lastPosition := next.checkpoint.saved_position
  have generation := congrArg CommitAttemptId.generation same
  have position := congrArg CommitAttemptId.phase same
  have counts := setup.commitRecovery_same_generation_length path _ _ rfl rfl generation.symm
  have firstBound := ProtocolState.remaining_le_instructionCount setup.program
    (witness.checkpoint.residual.lift
      (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source))
  have lastBound := ProtocolState.remaining_le_instructionCount setup.program
    (next.checkpoint.residual.lift
      (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source))
  have unchanged : (⟨_, next.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, witness.checkpoint.trace⟩ := by
    apply path.eq_of_trace_length_eq
    change witness.checkpoint.trace.length = next.checkpoint.trace.length
    change instructionCount setup.program - ProtocolState.remaining setup.program
      (witness.checkpoint.residual.lift
        (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source)) =
        anchor.execution.application.attempt.phase at firstPosition
    change instructionCount setup.program - ProtocolState.remaining setup.program
      (next.checkpoint.residual.lift
        (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source)) =
        current.execution.application.attempt.phase at lastPosition
    change ProtocolState.remaining setup.program
      (next.checkpoint.residual.lift
        (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source)) +
      next.checkpoint.trace.length = ProtocolState.remaining setup.program
      (witness.checkpoint.residual.lift
        (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source)) +
        witness.checkpoint.trace.length at counts
    omega
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨input, _selected, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan input
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler anchorTrace)
  have progress := phase_attempt_progress_of_prefix runtime leaks (menu) initial initialized
    horizon scheduler anchor current anchorTrace currentTrace kept ordered
  have saved := (progress.2.2 same.symm).symm
  let represented : RecoverySourceCheckpoint setup mode current.execution.application :=
    witness.checkpoint.transfer saved generation position
  have representation : (⟨_, represented.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, next.checkpoint.trace⟩ :=
    (witness.checkpoint.transfer_history saved generation position).trans unchanged.symm
  have sourceMemory : represented.source.history = next.checkpoint.source.history := by
    have points := congrArg CommitRecoveryState.point
      (Option.some.inj (congrArg History.state representation))
    have memory := congrArg (ProtocolState.history setup.program) points
    change ProtocolState.history setup.program
        (represented.residual.lift (ProtocolState.entry represented.residual.tail
          represented.source)) = ProtocolState.history setup.program
        (next.checkpoint.residual.lift (ProtocolState.entry next.checkpoint.residual.tail
          next.checkpoint.source)) at memory
    simpa only [represented.history, next.checkpoint.history, ProtocolState.history_entry]
      using memory
  let canonical : RecoverySourceWitness setup mode plan current.execution.application := {
    next with
    checkpoint := represented
    aligned := fun who active => (congrFun sourceMemory who).trans (next.aligned who active)
    chronology := ⟨(congrArg (fun history : setup.commitRecoveryProtocol.History =>
      setup.recoveryAddressWord history.trace) representation).trans next.chronology.addresses,
        next.chronology.consumed⟩
    origins := representation.symm ▸ next.origins }
  have canonicalArchived : canonical.checkpoint.ArchivedProposals current.execution.network.inputs
    :=
    by
      intro who active
      have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
        (⟨history.state, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive current.execution.network.inputs))
            history.trace⟩ : setup.proposalRecoveryProtocol.History)) representation
      exact (congrArg (fun history : setup.proposalRecoveryProtocol.History =>
        setup.proposalRecoveryArchive who
          (setup.proposalRecoveryModel.infoOf who history.trace)) lifted).trans
            (nextArchived who active)
  exact ⟨canonical, canonicalArchived,
    witness.checkpoint.transfer_history saved generation position, saved, rfl⟩

/-- The actual raw close retains its supplied checkpoint before normalization. -/
theorem RecoverySourceWitness.raw_closing_checkpoint
    (before ending : (app).Control)
    (witness : RecoverySourceWitness setup mode plan before.execution.application)
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt) :
    ∃ next : RecoverySourceWitness setup mode plan
        ({before.execution.application with current := raw} : PhaseRuntimeState graph),
      next.checkpoint = witness.checkpoint.transfer
        (other := {before.execution.application with current := raw}) rfl rfl rfl ∧
      (⟨_, next.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
        ⟨_, witness.checkpoint.trace⟩ := by
  rcases effect with ⟨id, message, result, found, moved, handled, rfl⟩ |
      ⟨command, result, moved, supported, rfl⟩
  · have selected : ending.execution.application =
        ((app).handle before.execution.application message).getD before.execution.application := by
      have actual := moved
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at actual
      have stateEq := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff _ _).mp actual)
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] using stateEq
    have allowed : (message.payload.tokenValid before.execution.application.attempt &&
        before.execution.application.allows message.payload.packet.call &&
          !before.execution.application.current.excludedCall message.payload.packet.call) = true
            := by
      by_contra invalid
      have absent : before.execution.application.handle runtime message = none := by
        simp only [PhaseRuntimeState.handle, ite_eq_right invalid]
      have same : ending.execution.application = before.execution.application := by
        simpa only [show (app).handle before.execution.application message = none from absent,
          Option.getD_none] using selected
      exact changed (congrArg PhaseRuntimeState.attempt same)
    exact ⟨witness.raw_handle runtime message result allowed handled, rfl, rfl⟩
  · have authorized : before.execution.application.commandAllowed command = true := by
      by_contra denied
      have stutters : (app).environment before.execution.application command =
          PMF.pure before.execution.application := by
        simp only [phaseApplication, PhaseRuntimeState.environment, ite_eq_right denied]
      have actual := moved
      simp only [ReactiveApplication.Execution.environmentStep, stutters, PMF.pure_map] at actual
      have same := congrArg (fun execution : (app).Execution => execution.application)
        ((PMF.mem_support_pure_iff _ _).mp actual)
      exact changed (congrArg PhaseRuntimeState.attempt same)
    exact ⟨witness.raw_environment runtime command result authorized supported, rfl, rfl⟩

end Vegas
