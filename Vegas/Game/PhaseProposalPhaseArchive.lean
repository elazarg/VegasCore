/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalDeltaArchive
import Vegas.Game.PhaseProposalArchivedDelta
import Vegas.Game.PhaseProposalReplayCoverage
import Vegas.Game.PhaseProposalReplayArchive
import Vegas.Source.CommitRecoveryCursor

/-! # Exact proposal archive of one actual consumed publication phase -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Actual compiler replay and counted submission provenance determine both
archive inclusions. In particular failed receipts and failed guards are retained. -/
theorem consumed_publication_phase_archive
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : ((toEventGraph setup.program).withMode mode).RevealRelaxedOrdered)
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (installed : current.execution.application.phases.head? = some phase)
    (kind : phase.kind = .reveal)
    (image : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (origins : PhaseProposal.OpeningOrigins current.execution.network.inputs image)
    (kept : KeepsStore current.execution.application.current.native image)
    (failures : current.execution.application.entry.native.PublicFailureExtension image)
    (saved : current.execution.application.entry.native.config.cut.IsPrefix phase.low)
    (before after : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some before))
    (next : setup.commitRecoveryProtocol.Trace (some after)) (fuel : Nat)
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, prior⟩ ⟨_, next⟩)
    (extension : NativeSourceReplayExtension setup image before.generation prior next)
    (sameGeneration : before.generation = after.generation)
    (generation : before.generation = current.execution.application.attempt.generation)
    (entryExcluded : before.excluded = current.execution.application.entry.excluded)
    (firstRank : instructionCount setup.program -
      ProtocolState.remaining setup.program before.point = phase.low)
    (lastRank : instructionCount setup.program -
      ProtocolState.remaining setup.program after.point = phase.high) :
    replayProposalArchive setup
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive current.execution.network.inputs))
        ((proposalSourceSteps setup next).drop prior.length) =
      (PhaseProposal.sourceArchive current.execution.network.inputs).filter
        (fun proposal => proposal.address.phase = current.execution.application.attempt.phase) := by
  classical
  let archive := PhaseProposal.sourceArchive current.execution.network.inputs
  let labels := nativeArchiveLabels setup archive
  have countedLength := setup.commitRecovery_same_generation_length reached before after rfl rfl
    sameGeneration
  change ProtocolState.remaining setup.program after.point + next.length =
    ProtocolState.remaining setup.program before.point + prior.length at countedLength
  have beforeBound := ProtocolState.remaining_le_instructionCount setup.program before.point
  have afterBound := ProtocolState.remaining_le_instructionCount setup.program after.point
  have count : next.length - prior.length = phase.high - phase.low := by omega
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler rawTrace
  have phaseMember := suffix.subset (List.mem_of_mem_head? installed)
  have low : current.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler rawTrace
  have oldSubset : image.failureOwnersBefore phase.low ⊆
      current.execution.application.entry.excluded := by
    intro owner member
    obtain ⟨event, lower, acting, failed⟩ := (Finset.mem_filter.mp member).2
    exact coverage.saved.covered event owner acting
      ((failures.failures event ((saved.2 event).mpr lower)).mp failed)
  have initialScan : before.excluded = current.execution.application.entry.excluded ∪
      image.failureOwnersBefore
        (instructionCount setup.program - ProtocolState.remaining setup.program before.point) := by
    rw [firstRank, Finset.union_eq_left.mpr oldSubset]
    exact entryExcluded
  obtain ⟨events, points, chain, head, steps, annotated, eventLength, cursors⟩ := extension
  have newSteps : (proposalSourceSteps setup next).drop prior.length = events := by
    rw [← proposalSourceSteps_length setup prior, steps, List.drop_left]
  apply Finset.ext
  intro proposal
  constructor
  · intro member
    obtain ⟨event, eventMember, decoded⟩ := (mem_replayProposalArchive setup labels _ proposal).mp
      member
    rw [newSteps] at eventMember
    obtain ⟨first, last, source, _target, moved, disclosure, _pointMember⟩ :=
      annotated event eventMember
    let state := CommitRecoveryState.atPoint first.1 first.2 before.generation
    have source' : event.source = some state := source
    obtain ⟨index, bound, selected⟩ := List.mem_iff_getElem.mp eventMember
    have cursor := cursors index bound
    rw [selected, source] at cursor
    simp only [Option.map_some, CommitRecoveryState.atPoint] at cursor
    have rank := Option.some.inj cursor
    have lower : phase.low ≤ instructionCount setup.program -
        ProtocolState.remaining setup.program state.point := by
      dsimp only [state, CommitRecoveryState.atPoint]
      omega
    have upper : instructionCount setup.program -
        ProtocolState.remaining setup.program state.point < phase.high := by
      dsimp only [state, CommitRecoveryState.atPoint]
      omega
    have archived := source_replay_delta_in_archive setup mode runtime leaks bounds plan maximal
      ordered inputs horizon scheduler current trace phase installed kind image origins kept event
      state source' moved.2.2.1 disclosure generation lower upper proposal decoded
    have decoded' : setup.proposalRecoveryProposalOf (some state)
        (setup.proposalRecoveryLiftJoint labels event) = some proposal := by
      simpa only [source'] using decoded
    obtain ⟨_owner, _acting, _notCommit, _surviving, _exposed, _stored, address⟩ :=
      source_proposal_readback_origin setup image state moved.2.2.1 _ proposal decoded'
    have bounded : instructionCount setup.program -
        ProtocolState.remaining setup.program state.point <
          ((toEventGraph setup.program).withMode mode).order.eventCount :=
      upper.trans_le phase.bounded
    let nativeEvent : ((toEventGraph setup.program).withMode mode).EventId :=
      ⟨instructionCount setup.program - ProtocolState.remaining setup.program state.point, bounded⟩
    have inside : nativeEvent ∈ phase.events := (phase.mem_events nativeEvent).mpr ⟨lower, upper⟩
    have static := publicationBlockLow_of_phase setup.program mode plan maximal phase phaseMember
      kind nativeEvent inside
    refine Finset.mem_filter.mpr ⟨archived, ?_⟩
    rw [address]
    change setup.program.publicationBlockLow nativeEvent.val = _
    exact static.trans low.symm
  · intro member
    obtain ⟨archived, currentPhase⟩ := Finset.mem_filter.mp member
    obtain ⟨nativeEvent, inside, address⟩ :=
      PhaseProposal.archived_proposal_in_installed_phase runtime leaks bounds plan ordered inputs
        horizon scheduler current trace phase installed proposal archived currentPhase
    have interval := (phase.mem_events nativeEvent).mp inside
    obtain ⟨event, state, eventMember, source, sourceGeneration, ranked, notCommit, readback,
      _disclosure, scan⟩ := native_replay_event_at_rank setup mode image before.generation before
        prior next ⟨events, points, chain, head, steps, annotated, eventLength, cursors⟩
        current.execution.application.entry.excluded initialScan nativeEvent.val
        (by omega) (by have nonempty := phase.nonempty; omega)
    have decoded := archived_proposal_source_delta setup mode runtime leaks bounds plan maximal
      ordered inputs horizon scheduler current trace phase installed kind image kept failures saved
      event state source readback notCommit (sourceGeneration.trans generation) nativeEvent inside
      ranked scan proposal archived address
    exact (mem_replayProposalArchive setup labels _ proposal).mpr ⟨event, eventMember, decoded⟩

end Vegas
