/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalFreshTerminal
import Vegas.Game.RecoverySameAttemptWitness
import Vegas.Pending.PhaseProposalAcceptedHistory

/-! # Archive continuation from the supplied completed phase witness -/

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

omit [Fintype Player] in
private theorem checkpoint_cast_archive
    {state other : PhaseRuntimeState graph} (same : state = other)
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (messages : List (Message Player (CommitAttemptPacket graph))) :
    (same ▸ checkpoint).ArchivedProposals messages ↔ checkpoint.ArchivedProposals messages := by
  cases same
  rfl

private theorem proposalDelta_cast_target
    {state middle other : PhaseRuntimeState graph} (same : middle = other)
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode middle) :
    checkpoint.ProposalDelta plan (same ▸ next) ↔ checkpoint.ProposalDelta plan next := by
  cases same
  rfl

/-- The original closing primitive and the supplied completed witness feed
the existing normalizer. Its chosen checkpoint retains the exact archive and
full source terminal law before any payoff projection. -/
theorem RecoverySourceWitness.completed_normalized_archived_source
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (before ending : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (beforeWitness : RecoverySourceWitness setup mode plan before.execution.application)
    (beforeArchived : beforeWitness.checkpoint.ArchivedProposals before.execution.network.inputs)
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (rawWitness : RecoverySourceWitness setup mode plan
      ({ before.execution.application with current := raw } : PhaseRuntimeState graph))
    (rawCheckpoint : rawWitness.checkpoint = beforeWitness.checkpoint.transfer
      (other := { before.execution.application with current := raw }) rfl rfl rfl)
    (phase : RuntimePhase graph) (rest : List (RuntimePhase graph))
    (beforePhases : before.execution.application.phases = phase :: rest)
    (finished : phase.Finished (phase.drain raw))
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } : PhaseRuntimeState graph).normalize)
    (settled : ending.execution.application = PhaseRuntimeState.settle rest
      before.execution.application.generation (phase.drain raw) (phase.drain raw)
        before.execution.application.retired)
    (completed : RecoverySourceWitness setup mode plan
      (⟨rest, before.execution.application.generation, phase.drain raw, phase.drain raw,
        before.execution.application.retired⟩ : PhaseRuntimeState graph))
    (phaseDelta : rawWitness.checkpoint.ProposalDelta plan completed.checkpoint)
    (sourceCertificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (sourceProfile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who) :
    let labels := nativeArchiveLabels setup
      (PhaseProposal.sourceArchive ending.execution.network.inputs)
    ∃ next : RecoverySourceWitness setup mode plan
        (PhaseRuntimeState.settle rest before.execution.application.generation
          (phase.drain raw) (phase.drain raw) before.execution.application.retired),
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, completed.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩) ∧
      setup.proposalRecoveryModel.runBehavioralTerminalFrom sourceCertificate sourceProfile
          ⟨_, setup.proposalRecoveryLiftTrace labels completed.checkpoint.trace⟩ =
        setup.proposalRecoveryModel.runBehavioralTerminalFrom sourceCertificate sourceProfile
          ⟨_, setup.proposalRecoveryLiftTrace labels next.checkpoint.trace⟩ ∧
      completed.checkpoint.ProposalDelta plan next.checkpoint ∧
      next.checkpoint.ArchivedProposals ending.execution.network.inputs := by
  intro labels
  obtain ⟨next, nextPath, sourceKernel, nextDelta⟩ :=
    completed.fresh_normalized_terminal_law mode plan maximal rest
      before.execution.application.generation (phase.drain raw)
        before.execution.application.retired sourceCertificate sourceProfile labels
  refine ⟨next, nextPath, sourceKernel, nextDelta, ?_⟩
  let rawState : PhaseRuntimeState graph :=
    { before.execution.application with current := raw }
  let completedState : PhaseRuntimeState graph :=
    ⟨rest, before.execution.application.generation, phase.drain raw,
      phase.drain raw, before.execution.application.retired⟩
  have origins := PhaseProposal.openingOrigins_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler before
      ((menu).toRawTrace initial horizon scheduler prior)
  have rawFrame : PhaseProposal.NormalizationFrame runtime leaks before
      rawState := by
    rcases effect with ⟨id, message, result, found, moved, handled, rawEq⟩ |
        ⟨command, result, moved, sampled, rawEq⟩
    · have present := ((app).retained_envelopes_mem_inputs before.execution
        ((app).history_provenance initial horizon scheduler
          ((menu).toRawTrace initial horizon scheduler prior))
        ((app).history_inputRecall initial horizon scheduler
          ((menu).toRawTrace initial horizon scheduler prior))).lookup
            id message found
      change PhaseProposal.NormalizationFrame runtime leaks before
        ({ before.execution.application with current := raw } : PhaseRuntimeState graph)
      rw [rawEq]
      exact PhaseProposal.NormalizationFrame.inclusion runtime leaks before
        origins message present result handled
    · change PhaseProposal.NormalizationFrame runtime leaks before
        ({ before.execution.application with current := raw } : PhaseRuntimeState graph)
      rw [rawEq]
      exact PhaseProposal.NormalizationFrame.environment runtime leaks before
        origins command result sampled
  have inherited : before.execution.application.current.excluded ⊆
      raw.excluded := by
    rcases effect with ⟨id, message, result, found, moved, handled, rfl⟩ |
        ⟨command, result, moved, sampled, rfl⟩
    · exact before.execution.application.current.inclusionResult_excluded_subset
        message.payload.packet.call result
    · exact before.execution.application.current.environmentResult_excluded_subset
        command result
  have closingInputs : ending.execution.network.inputs =
      before.execution.network.inputs := by
    rcases effect with ⟨id, message, result, found, moved, handled, rawEq⟩ |
        ⟨command, result, moved, sampled, rawEq⟩
    · exact (app).environmentStep_inputs before.execution ending.execution
        (.include id) moved
    · exact (app).environmentStep_inputs before.execution ending.execution
        (.application command) moved
  have old : rawWitness.checkpoint.ArchivedProposals
      before.execution.network.inputs := by
    intro who active
    rw [rawCheckpoint]
    exact beforeArchived who (fun absent => active (inherited absent))
  have adjacent := rawWitness.order.frontier.adjacent
  change before.execution.application.phases.IsChain
    (fun first last => first.high = last.low) at adjacent
  rw [beforePhases] at adjacent
  have afterPhase : rawState.attempt.phase < completedState.attempt.phase := by
    have rawLow : rawState.attempt.phase = phase.low := by
      simp only [rawState, PhaseRuntimeState.attempt, beforePhases,
        List.head?_cons, Option.map_some, Option.getD_some]
    rw [rawLow]
    change phase.low < PhaseRuntimeState.phaseLow rest
    cases rest with
    | nil => exact phase.nonempty.trans_le phase.bounded
    | cons next rest =>
        exact phase.nonempty.trans_eq (List.isChain_cons_cons.mp adjacent).1
  have normalizedPhase : completedState.attempt.phase ≤
      (PhaseRuntimeState.settle rest before.execution.application.generation
        (phase.drain raw) (phase.drain raw)
          before.execution.application.retired).attempt.phase :=
    (PhaseRuntimeState.settle_namespace rest
      before.execution.application.generation (phase.drain raw) (phase.drain raw)
        before.execution.application.retired completed.order.frontier.adjacent).2
  have combined := RecoverySourceCheckpoint.ProposalDelta.trans plan
    rawWitness.checkpoint completed.checkpoint next.checkpoint phaseDelta nextDelta
      afterPhase.le
      normalizedPhase (by
        intro otherRuntime otherLeaks external frame
        have imageOrigins := frame.currentOrigins.drain raw.excluded phase
        exact PhaseProposal.NormalizationFrame.future external completedState
          (frame.lower.trans_lt afterPhase) imageOrigins imageOrigins)
  have rawSettled : rawState.normalize = PhaseRuntimeState.settle rest
      before.execution.application.generation (phase.drain raw) (phase.drain raw)
        before.execution.application.retired := normalized.symm.trans settled
  let normalizedCheckpoint : RecoverySourceCheckpoint setup mode
      rawState.normalize := rawSettled.symm ▸ next.checkpoint
  have delta : rawWitness.checkpoint.ProposalDelta plan normalizedCheckpoint := by
    exact (proposalDelta_cast_target setup mode plan rawSettled.symm
      rawWitness.checkpoint next.checkpoint).mpr combined
  have normalizedArchive := RecoverySourceCheckpoint.ArchivedProposals.normalize
    plan rawWitness.checkpoint normalizedCheckpoint runtime leaks bounds
      (setup.initialLaw.map encodeInputs)
      horizon scheduler before prior rawFrame rawWitness.order.frontier.adjacent
        old delta
  rw [closingInputs]
  exact (checkpoint_cast_archive setup mode rawSettled.symm next.checkpoint
    before.execution.network.inputs).mp normalizedArchive
end Vegas
