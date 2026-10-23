/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalArchiveValue
import Vegas.Game.PhaseProposalLabels
import Vegas.Game.PhaseProposalActor
import Vegas.Pending.PhaseProposalFailure
import Vegas.Source.CommitRecoveryRevealMenu
import Vegas.Pending.PhasePlanSuffix

/-! # Submitted counted proposals are exposed by the actual labeled source step -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem archived_proposal_source_delta
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
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
    (kept : KeepsStore current.execution.application.current.native image)
    (failures : current.execution.application.entry.native.PublicFailureExtension image)
    (saved : current.execution.application.entry.native.config.cut.IsPrefix phase.low)
    (event : setup.commitRecoveryProtocol.StepEvent)
    (state : CommitRecoveryState setup.program) (source : event.source = some state)
    (readback : NativeProposalReadback image 0 setup.program state.point)
    (notCommit : ProtocolState.atCommit setup.program state.point = false)
    (generation : state.generation = current.execution.application.attempt.generation)
    (nativeEvent : ((toEventGraph setup.program).withMode mode).EventId)
    (inside : nativeEvent ∈ phase.events)
    (ranked : nativeEvent.val = instructionCount setup.program -
      ProtocolState.remaining setup.program state.point)
    (scan : state.excluded = current.execution.application.entry.excluded ∪
      image.failureOwnersBefore nativeEvent.val)
    (proposal : ProposalRecoveryProposal L)
    (member : proposal ∈ PhaseProposal.sourceArchive current.execution.network.inputs)
    (address : proposal.address =
      PhaseProposal.sourceAddress ⟨current.execution.application.attempt, nativeEvent⟩) :
    setup.proposalRecoveryProposalOf event.source
      (setup.proposalRecoveryLiftJoint
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive current.execution.network.inputs))
        event) = some proposal := by
  let archive := PhaseProposal.sourceArchive current.execution.network.inputs
  let labels := nativeArchiveLabels setup archive
  obtain ⟨rawProposal, archived, decoded⟩ := (PhaseProposal.mem_sourceArchive _ _).mp member
  have coordinate := PhaseProposal.sourceAddress_injective
    ((PhaseProposal.sourceProposal?_address rawProposal proposal decoded).symm.trans address)
  rcases rawProposal with ⟨coordinate', raw⟩
  change coordinate' = ⟨current.execution.application.attempt, nativeEvent⟩ at coordinate
  subst coordinate'
  obtain ⟨message, submitted, proposed⟩ := (PhaseProposal.mem_archive _ _).mp archived
  have safe := PhaseProposal.submitted_proposal_owner_not_in_scan runtime leaks bounds plan
    ordered inputs horizon scheduler current trace phase kind message submitted _ raw proposed
    rfl inside saved image kept failures
  have surviving : message.sender ∉ state.excluded := by simpa only [scan] using safe
  obtain ⟨_before, _prior, _material, _candidate, _retained, _active, request, _call, _offered,
    _stamp⟩ := PhaseProposal.submitted_proposal_callback runtime leaks bounds plan ordered inputs
      horizon scheduler current trace message submitted _ raw proposed
  have acting : ProtocolState.actor setup.program state.point = some message.sender :=
    (source_actor_at_compiled_rank setup.program mode state.point nativeEvent ranked).trans
      request.2.2.2.1
  have legal : setup.commitRecoveryProtocol.Legal (some state) event.joint := by
    simpa only [source] using event.isLegal
  obtain ⟨name, bit, chosen⟩ := setup.commitRecovery_reveal_joint_of_legal state event.joint legal
    message.sender acting surviving notCommit
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler rawTrace
  have phaseMember := suffix.subset (List.mem_of_mem_head? installed)
  have low : current.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  have static := publicationBlockLow_of_phase setup.program mode plan maximal phase phaseMember
    kind nativeEvent inside
  have requested : labels event message.sender = true := by
    apply (nativeArchiveLabels_some setup archive event message.sender state source).mpr
    refine ⟨proposal, member, ?_⟩
    rw [address]
    change (⟨current.execution.application.attempt.phase,
      current.execution.application.attempt.generation, nativeEvent.val⟩ :
        ProposalRecoveryAddress) = _
    rw [← ranked, static, generation, low]
  have disclosed : (((setup.proposalRecoveryLiftJoint labels event) message.sender).map
      (·.discloses)).getD false = true := by
    simp only [Setup.proposalRecoveryLiftJoint, chosen, Option.map_some, Option.getD_some]
    cases bit <;> simp only [ProposalRecoveryMove.label, ProposalRecoveryMove.ordinary,
      ProposalRecoveryMove.discloses, OwnAction.disclosure, requested,
      Bool.false_or, Bool.true_or]
  have stored := PhaseProposal.archived_proposal_image_value runtime leaks bounds plan ordered
    inputs horizon scheduler current trace proposal member nativeEvent address image kept
  have delta := source_proposal_delta_of_readback setup image state readback message.sender
    acting notCommit surviving ⟨current.execution.application.attempt, nativeEvent⟩ proposal.payload
    proposal.value ranked (static.trans low.symm) generation stored
    (setup.proposalRecoveryLiftJoint labels event) disclosed
  have canonical : (⟨PhaseProposal.sourceAddress
      ⟨current.execution.application.attempt, nativeEvent⟩, proposal.payload, proposal.value⟩ :
        ProposalRecoveryProposal L) = proposal := by
    cases proposal
    cases address
    rfl
  simpa only [source, canonical] using delta

end Vegas
