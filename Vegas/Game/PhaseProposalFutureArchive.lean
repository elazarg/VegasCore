/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLabels
import Vegas.Game.PhaseProposalDisclosure
import Vegas.Game.PhaseProposalAddress
import Vegas.Game.PhaseProposalArchiveBounds
import Vegas.Game.PhaseProposalReplayArchive
import Vegas.Source.CommitRecoveryCursor
import Vegas.Pending.PhaseProposalFuture

/-! # Automatic future publication images cannot add source proposal deltas -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- This covers a future publication interval drained inside the SAME
external environment step. It uses the actual earlier counted anchor and does
not invent an intermediate counted execution for that automatically skipped phase. -/
theorem source_replay_future_delta_none
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (member : phase ∈ plan.phases) (kind : phase.kind = .reveal)
    (future : current.execution.application.attempt.phase < phase.low)
    (image : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (origins : PhaseProposal.OpeningOrigins current.execution.network.inputs image)
    (event : setup.commitRecoveryProtocol.StepEvent)
    (state : CommitRecoveryState setup.program) (source : event.source = some state)
    (readback : NativeProposalReadback image 0 setup.program state.point)
    (disclosure : NativeDisclosureReadback image 0 setup.program state.point state.excluded
      event.joint)
    (lower : phase.low ≤ instructionCount setup.program -
      ProtocolState.remaining setup.program state.point)
    (upper : instructionCount setup.program -
      ProtocolState.remaining setup.program state.point < phase.high) :
    setup.proposalRecoveryProposalOf event.source
      (setup.proposalRecoveryLiftJoint
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive current.execution.network.inputs))
        event) = none := by
  let archive := PhaseProposal.sourceArchive current.execution.network.inputs
  let labels := nativeArchiveLabels setup archive
  let joint := setup.proposalRecoveryLiftJoint labels event
  change setup.proposalRecoveryProposalOf event.source joint = none
  cases decoded : setup.proposalRecoveryProposalOf event.source joint with
  | none => rfl
  | some proposal =>
      have decoded' : setup.proposalRecoveryProposalOf (some state) joint = some proposal := by
        simpa only [source] using decoded
      obtain ⟨owner, acting, _notCommit, surviving, exposed, _stored, _address⟩ :=
        source_proposal_readback_origin setup image state readback joint proposal decoded'
      by_cases semantic : OwnAction.disclosure ((event.joint owner).map (·.action)) = true
      · obtain ⟨actual, payload, publication, action, ranked, recorded, disclosed⟩ :=
          disclosure owner acting surviving semantic
        simp only [Nat.zero_add] at ranked
        have inside : actual ∈ phase.events := (phase.mem_events actual).mpr
          ⟨by omega, by omega⟩
        have absent := PhaseProposal.future_publication_image_nondisclosing runtime leaks bounds
          plan inputs horizon scheduler current trace phase member future image origins
          ⟨actual, action⟩ inside recorded
        have present : PhaseProposal.publicationDiscloses
            (((toEventGraph setup.program).withMode mode).outputLayout actual) action = true :=
          (PhaseProposal.publicationDiscloses_cast publication action).symm.trans disclosed
        rw [absent] at present
        cases present
      · have silent := Bool.eq_false_of_not_eq_true semantic
        have requested := liftJoint_requested_of_no_disclosure setup labels event owner silent
          exposed
        obtain ⟨actual, archived, address⟩ :=
          (nativeArchiveLabels_some setup archive event owner state source).mp requested
        let initial := inputs.map (PhaseRuntimeState.initial plan)
        have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
          initial horizon scheduler trace
        have bounded := PhaseProposal.sourceArchive_phase_le runtime leaks plan inputs horizon
          scheduler current rawTrace actual archived
        let rank := instructionCount setup.program - ProtocolState.remaining setup.program
          state.point
        let nativeEvent : ((toEventGraph setup.program).withMode mode).EventId :=
          ⟨rank, upper.trans_le phase.bounded⟩
        have inside : nativeEvent ∈ phase.events := (phase.mem_events nativeEvent).mpr
          ⟨lower, upper⟩
        have static := publicationBlockLow_of_phase setup.program mode plan maximal phase member
          kind nativeEvent inside
        have phaseAddress := congrArg ProposalRecoveryAddress.phase address
        change actual.address.phase = setup.program.publicationBlockLow rank at phaseAddress
        rw [static] at phaseAddress
        omega


/-- A future publication interval drained during one external step adds no
proposal to the very same selected source history. -/
theorem consumed_future_publication_phase_archive_empty
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (member : phase ∈ plan.phases) (kind : phase.kind = .reveal)
    (future : current.execution.application.attempt.phase < phase.low)
    (image : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (origins : PhaseProposal.OpeningOrigins current.execution.network.inputs image)
    (before after : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some before))
    (next : setup.commitRecoveryProtocol.Trace (some after)) (fuel : Nat)
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, prior⟩ ⟨_, next⟩)
    (extension : NativeSourceReplayExtension setup image before.generation prior next)
    (sameGeneration : before.generation = after.generation)
    (firstRank : instructionCount setup.program -
      ProtocolState.remaining setup.program before.point = phase.low)
    (lastRank : instructionCount setup.program -
      ProtocolState.remaining setup.program after.point = phase.high) :
    replayProposalArchive setup
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive current.execution.network.inputs))
        ((proposalSourceSteps setup next).drop prior.length) = ∅ := by
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
  obtain ⟨events, _points, _chain, _head, steps, annotated, length, cursors⟩ := extension
  have newSteps : (proposalSourceSteps setup next).drop prior.length = events := by
    rw [← proposalSourceSteps_length setup prior, steps, List.drop_left]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro proposal archived
  obtain ⟨event, present, decoded⟩ :=
    (mem_replayProposalArchive setup labels _ proposal).mp archived
  rw [newSteps] at present
  obtain ⟨first, _last, source, _target, moved, disclosure, _pointMember⟩ :=
    annotated event present
  obtain ⟨index, bound, selected⟩ := List.mem_iff_getElem.mp present
  have cursor := cursors index bound
  rw [selected, source] at cursor
  simp only [Option.map_some, CommitRecoveryState.atPoint] at cursor
  have ranked := Option.some.inj cursor
  have lower : phase.low ≤ instructionCount setup.program -
      ProtocolState.remaining setup.program first.1 := by omega
  have upper : instructionCount setup.program -
      ProtocolState.remaining setup.program first.1 < phase.high := by omega
  have silent := source_replay_future_delta_none setup mode runtime leaks bounds plan maximal
    inputs horizon scheduler current trace phase member kind future image origins event
    (CommitRecoveryState.atPoint first.1 first.2 before.generation) source moved.2.2.1 disclosure
    lower upper
  rw [silent] at decoded
  cases decoded

end Vegas
