/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalActor
import Vegas.Game.PhaseProposalReplayArchive
import Vegas.Source.CommitRecoveryCursor

/-! # Actual singleton sample replays disclose no opening proposal -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem source_delta_none_of_ownerless
    (setup : Setup (Player := Player) (L := L)) {graph : Vegas.EventGraph Player L}
    (native : EventGraphRuntime.State graph) (state : CommitRecoveryState setup.program)
    (readback : NativeProposalReadback native 0 setup.program state.point)
    (ownerless : ProtocolState.actor setup.program state.point = none)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryProposalOf (some state) joint = none := by
  let masked := fun who => if who ∈ state.excluded then none else joint who
  have empty := readback masked
  simp only [nativeRecoveryProposal?, ownerless, Option.bind_none, ite_self] at empty
  change Option.map _ (ProtocolState.recoveryProposal setup.program state.point masked) = none
  cases proposed : ProtocolState.recoveryProposal setup.program state.point masked with
  | none => rfl
  | some pair => rw [proposed, Option.map_some] at empty; cases empty

omit [DecidableEq Player] in
private theorem actor_none_of_sample {graph : Vegas.EventGraph Player L}
    (event : graph.EventId) (payload : L.Ty)
    (output : graph.outputLayout event = .publicData payload) : graph.actor? event = none := by
  cases viewed : nodeView graph event with
  | sample actual law outputEq codeEq =>
      exact (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
  | bind owner actual outputEq codeEq => cases outputEq.symm.trans output
  | resolve owner actual binding checks outputEq codeEq => cases outputEq.symm.trans output

/-- The actual compiled sample interval has no owned source action at any
replayed prestate. Proposal labels cannot add a disclosure at these steps. -/
theorem consumed_sample_phase_archive_empty
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (kind : phase.kind = .sample)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (before after : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some before))
    (next : setup.commitRecoveryProtocol.Trace (some after)) (fuel : Nat)
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, prior⟩ ⟨_, next⟩)
    (extension : NativeSourceReplayExtension setup native before.generation prior next)
    (sameGeneration : before.generation = after.generation)
    (firstRank : instructionCount setup.program -
      ProtocolState.remaining setup.program before.point = phase.low)
    (lastRank : instructionCount setup.program -
      ProtocolState.remaining setup.program after.point = phase.high)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    replayProposalArchive setup labels ((proposalSourceSteps setup next).drop prior.length) =
      ∅ := by
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
  intro proposal member
  obtain ⟨event, eventMember, decoded⟩ :=
    (mem_replayProposalArchive setup labels _ proposal).mp member
  rw [newSteps] at eventMember
  obtain ⟨first, _last, source, _target, moved, _disclosure, _pointMember⟩ :=
    annotated event eventMember
  obtain ⟨index, bound, selected⟩ := List.mem_iff_getElem.mp eventMember
  have cursor := cursors index bound
  rw [selected, source] at cursor
  simp only [Option.map_some, CommitRecoveryState.atPoint] at cursor
  have ranked := Option.some.inj cursor
  have lower : phase.low ≤ instructionCount setup.program -
      ProtocolState.remaining setup.program first.1 := by omega
  have upper : instructionCount setup.program -
      ProtocolState.remaining setup.program first.1 < phase.high := by omega
  let nativeEvent : ((toEventGraph setup.program).withMode mode).EventId :=
    ⟨instructionCount setup.program - ProtocolState.remaining setup.program first.1,
      upper.trans_le phase.bounded⟩
  have typed := phase.fields nativeEvent lower upper
  rw [kind] at typed
  obtain ⟨payload, output⟩ := typed
  have ownerless := (source_actor_at_compiled_rank setup.program mode first.1 nativeEvent rfl).trans
    (actor_none_of_sample nativeEvent payload output)
  rw [source] at decoded
  have silent := source_delta_none_of_ownerless setup native
    (CommitRecoveryState.atPoint first.1 first.2 before.generation) moved.2.2.1 ownerless
    (setup.proposalRecoveryLiftJoint labels event)
  rw [silent] at decoded
  cases decoded

end Vegas
