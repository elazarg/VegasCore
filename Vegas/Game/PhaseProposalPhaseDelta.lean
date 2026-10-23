/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalNormalization
import Vegas.Game.PhaseProposalCommitArchive
import Vegas.Game.PhaseProposalPhaseArchive
import Vegas.Game.PhaseProposalFutureArchive
import Vegas.Game.PhaseProposalSampleArchive
import Vegas.Game.PhaseProposalBucket

/-! # Actual noncommitment phase increments in source normalization -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace RecoverySourceCheckpoint

/-- Closing the selected physical commitment attempt adds no proposal,
including retry and exhaustion. No earlier source archive match is needed. -/
theorem commit_proposal_delta
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode nextState)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    {fuel : Nat} (reached : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (instructions : setup.recoveryJointRecall next.trace =
      (checkpoint.commitInstructionWord native).reverse ++
        setup.recoveryJointRecall checkpoint.trace) : ProposalDelta plan checkpoint next := by
  intro runtime leaks bounds inputs horizon scheduler anchor trace frame who
  dsimp only
  let archive := PhaseProposal.sourceArchive anchor.execution.network.inputs
  let labels := nativeArchiveLabels setup archive
  have unchanged := checkpoint.commit_proposal_archive native committing
    ⟨_, next.trace⟩ reached instructions labels who
  have empty : archive.filter (fun proposal => state.attempt.phase ≤ proposal.address.phase ∧
      proposal.address.phase < nextState.attempt.phase) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro proposal present
    obtain ⟨archived, lower, _upper⟩ := Finset.mem_filter.mp present
    have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
    have bounded := PhaseProposal.sourceArchive_phase_le runtime leaks plan inputs horizon
      scheduler anchor rawTrace proposal archived
    by_cases current : state.attempt.phase = anchor.execution.application.attempt.phase
    · obtain ⟨phases, _generation, _entry, _kept⟩ := frame.current current
      have anchorInstalled : anchor.execution.application.phases.head? = some phase := by
        rw [← phases, installed]
        rfl
      have noPackets := PhaseProposal.sourceArchive_nonpublication_bucket_empty runtime leaks
        bounds plan ((toEventGraph setup.program).withMode_revealRelaxedOrdered
          (toEventGraph_barrierOrdered setup.program) mode) inputs horizon scheduler anchor
              trace
        phase anchorInstalled (by simp only [kind]; decide)
      have equal : proposal.address.phase = anchor.execution.application.attempt.phase := by omega
      have included : proposal ∈ archive.filter (fun proposed =>
          proposed.address.phase = anchor.execution.application.attempt.phase) :=
        Finset.mem_filter.mpr ⟨archived, equal⟩
      rw [noPackets] at included
      exact Finset.notMem_empty proposal included
    · have ordered := frame.lower
      omega
  rw [empty, Finset.union_empty]
  exact unchanged

/-- The actual selected public replay contributes precisely the newly consumed
bucket. All packet membership is derived from the external counted history;
future automatically drained intervals use actual origin evidence instead. -/
theorem public_proposal_delta
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (next : RecoverySourceCheckpoint setup mode nextState)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (member : phase ∈ plan.phases)
    (notCommit : phase.kind ≠ .commitment)
    (boundary : nextState.attempt.phase = phase.high)
    (generation : nextState.generation = state.generation)
    (saved : state.entry.native.config.cut.IsPrefix phase.low)
    (failures : state.entry.native.PublicFailureExtension (phase.drain state.current).native)
    {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (replay : NativeSourceReplayExtension setup (phase.drain state.current).native state.generation
      checkpoint.trace next.trace) : ProposalDelta plan checkpoint next := by
  intro runtime leaks bounds inputs horizon scheduler anchor trace frame who
  dsimp only
  let archive := PhaseProposal.sourceArchive anchor.execution.network.inputs
  let labels := nativeArchiveLabels setup archive
  let first := CommitRecoveryState.atPoint
    (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      state.entry.excluded state.generation
  let last := CommitRecoveryState.atPoint
    (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
      nextState.entry.excluded nextState.generation
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have firstRank : instructionCount setup.program -
      ProtocolState.remaining setup.program first.point = phase.low :=
    checkpoint.saved_position.trans low
  have lastRank : instructionCount setup.program -
      ProtocolState.remaining setup.program last.point = phase.high :=
    next.saved_position.trans boundary
  have sameGeneration : first.generation = last.generation := generation.symm
  have replay' : NativeSourceReplayExtension setup (phase.drain state.current).native
      first.generation checkpoint.trace next.trace := replay
  have origins := frame.currentOrigins.drain state.current.excluded phase
  let rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have archiveBound : ∀ proposal ∈ archive,
      proposal.address.phase ≤ anchor.execution.application.attempt.phase := by
    intro proposal present
    exact PhaseProposal.sourceArchive_phase_le runtime leaks plan inputs horizon scheduler
      anchor rawTrace proposal present
  have bucket : archive.filter (fun proposal => state.attempt.phase ≤ proposal.address.phase ∧
      proposal.address.phase < nextState.attempt.phase) =
      archive.filter (fun proposal => proposal.address.phase = phase.low) := by
    apply Finset.ext
    intro proposal
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨present, lower, _upper⟩
      have bounded := (archiveBound proposal present).trans frame.lower
      exact ⟨present, by omega⟩
    · rintro ⟨present, equal⟩
      exact ⟨present, by omega, by have positive := phase.nonempty; omega⟩
  have added : replayProposalArchive setup labels
      ((proposalSourceSteps setup next.trace).drop checkpoint.trace.length) =
      archive.filter (fun proposal => proposal.address.phase = phase.low) := by
    by_cases current : state.attempt.phase = anchor.execution.application.attempt.phase
    · obtain ⟨phases, sameGen, entry, kept⟩ := frame.current current
      have anchorInstalled : anchor.execution.application.phases.head? = some phase := by
        rw [← phases, installed]
        rfl
      have anchorLow : anchor.execution.application.attempt.phase = phase.low :=
        current.symm.trans low
      cases kind : phase.kind with
      | commitment => exact (notCommit kind).elim
      | reveal =>
          have actual := consumed_publication_phase_archive setup mode runtime leaks bounds
            plan
            maximal ((toEventGraph setup.program).withMode_revealRelaxedOrdered
              (toEventGraph_barrierOrdered setup.program) mode) inputs horizon scheduler anchor
              trace
            phase anchorInstalled kind (phase.drain state.current).native origins
            (fun field value present => phase.drain_keepsStore state.current field value
              (kept field value present))
            (by simpa only [entry] using failures) (by simpa only [entry] using saved)
            first last checkpoint.trace next.trace fuel reached replay' sameGeneration
            sameGen (by simp only [first, CommitRecoveryState.atPoint, entry]) firstRank lastRank
          simpa only [anchorLow] using actual
      | sample =>
          have empty := consumed_sample_phase_archive_empty setup mode phase kind
            (phase.drain state.current).native first last checkpoint.trace next.trace fuel reached
            replay' sameGeneration firstRank lastRank labels
          have noPackets := PhaseProposal.sourceArchive_nonpublication_bucket_empty runtime leaks
            bounds plan ((toEventGraph setup.program).withMode_revealRelaxedOrdered
              (toEventGraph_barrierOrdered setup.program) mode) inputs horizon scheduler anchor
              trace
            phase anchorInstalled (by simp only [kind]; decide)
          simpa only [anchorLow, empty] using noPackets.symm
    · have future : anchor.execution.application.attempt.phase < phase.low := by
        have lower := frame.lower
        omega
      have noPackets := PhaseProposal.sourceArchive_future_bucket_empty runtime leaks plan inputs
        horizon scheduler anchor rawTrace phase.low future
      rw [noPackets]
      cases kind : phase.kind with
      | commitment => exact (notCommit kind).elim
      | reveal =>
          exact consumed_future_publication_phase_archive_empty setup mode runtime leaks bounds plan
            maximal inputs horizon scheduler anchor trace phase member kind future
            (phase.drain state.current).native origins first last checkpoint.trace next.trace fuel
            reached replay' sameGeneration firstRank lastRank
      | sample =>
          exact consumed_sample_phase_archive_empty setup mode phase kind
            (phase.drain state.current).native first last checkpoint.trace next.trace fuel reached
            replay' sameGeneration firstRank lastRank labels
  obtain ⟨events, _points, _chain, _head, steps, _annotated, _length, _cursors⟩ := replay
  have appended : (proposalSourceSteps setup next.trace).drop checkpoint.trace.length = events := by
    rw [← proposalSourceSteps_length setup checkpoint.trace, steps, List.drop_left]
  have archiveEq := proposalLift_archive_extension setup labels who checkpoint.trace next.trace
    events steps
  rw [← appended, added, ← bucket] at archiveEq
  exact archiveEq

end RecoverySourceCheckpoint
end Vegas
