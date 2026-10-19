/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalHistory
import Vegas.Game.PhaseSurvivingBindingSource
import Vegas.Compile.EventSourcePosition

/-! # Actual counted binding decisions have an enriched source history -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual counted fold and the surviving binding reconstruction use the
same checkpoint. The completed commitment prefix adds no proposal, so its
actual enriched lift retains the entire physical submitted archive. This is
an original source history; virtual typed repair is a separate refinement. -/
theorem phase_ready_binding_proposal_source
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (source : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = control.execution.application.entry.excluded ∧
      source.generation = control.execution.application.generation ∧
      setup.commitRecoveryPublic (some source) =
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase) ∧
      ProtocolState.actor setup.program source.point = some who ∧
      instructionCount setup.program - ProtocolState.remaining setup.program source.point =
        event.val ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who event
        ((serviceGraph setup mode).playerStore who
          control.execution.application.current.native.config.store)
        (ProtocolState.history setup.program source.point who) =
          some (ProtocolState.observe who setup.program source.point) ∧
      setup.recoveryAddressWord sourceTrace =
        control.execution.application.sourcePublicAddressWord plan event.val ∧
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who
          (setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup
              (PhaseProposal.sourceArchive control.execution.network.inputs))
            sourceTrace)) = PhaseProposal.sourceArchive control.execution.network.inputs := by
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler trace
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨source, sourceTrace, excluded, generation, signal, actor, played, _word, decoded,
      addresses, preserved⟩ := RecoverySourceCheckpoint.surviving_binding_source setup mode runtime
    leaks plan maximal horizon scheduler raw witness.checkpoint witness.aligned witness.chronology
      who event payload binding
      request
  let inputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have rawMapped := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler
    counted
  obtain ⟨phase, remaining, installed, kind, _inside⟩ :=
    phase_ready_binding_phase runtime leaks plan
    (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler rawMapped who
      event payload binding request.2.2.1
  have full := RecoverySourceCheckpoint.ArchivedProposals.binding runtime leaks bounds plan inputs
    horizon
    scheduler control counted witness.checkpoint archived phase
      (by rw [installed]; rfl) kind who request.2.2.2.2
  have position := decodeEventView?_position setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who event _ _ _ decoded
  have count := ProtocolView.position_add_remaining who setup.program source.point
  rw [position] at count
  refine ⟨source, sourceTrace, excluded, generation, signal, actor, by omega, played, decoded,
    addresses, ?_⟩
  exact (preserved _ who).trans full

end Vegas
