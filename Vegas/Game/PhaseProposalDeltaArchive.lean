/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalDisclosedArchive
import Vegas.Game.PhaseProposalArchiveValue
import Vegas.Game.PhaseProposalLabels

/-! # Each actual labeled replay delta belongs to the submitted archive -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open SourceProgram.Setup

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem typedProposal_ext (first second : ProposalRecoveryProposal L)
    (address : first.address = second.address)
    (value : (⟨first.payload, first.value⟩ : Sigma L.Val) = ⟨second.payload, second.value⟩) :
    first = second := by
  cases first
  cases second
  cases address
  cases value
  rfl

/-- Native labels are derived from submitted coordinates. Ordinary true
disclosures use their recorded completion; withheld labels use the actual
archive member and its successful binding readback. -/
theorem source_replay_delta_in_archive
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
    (origins : PhaseProposal.OpeningOrigins current.execution.network.inputs image)
    (kept : KeepsStore current.execution.application.current.native image)
    (event : setup.commitRecoveryProtocol.StepEvent)
    (sourceState : CommitRecoveryState setup.program) (source : event.source = some sourceState)
    (readback : NativeProposalReadback image 0 setup.program sourceState.point)
    (disclosure : NativeDisclosureReadback image 0 setup.program sourceState.point
      sourceState.excluded event.joint)
    (generation : sourceState.generation = current.execution.application.attempt.generation)
    (lower : phase.low ≤ instructionCount setup.program -
      ProtocolState.remaining setup.program sourceState.point)
    (upper : instructionCount setup.program -
      ProtocolState.remaining setup.program sourceState.point < phase.high)
    (proposal : ProposalRecoveryProposal L)
    (decoded : setup.proposalRecoveryProposalOf event.source
      (setup.proposalRecoveryLiftJoint
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive current.execution.network.inputs))
        event) = some proposal) :
    proposal ∈ PhaseProposal.sourceArchive current.execution.network.inputs := by
  let archive := PhaseProposal.sourceArchive current.execution.network.inputs
  let labels := nativeArchiveLabels setup archive
  let joint := setup.proposalRecoveryLiftJoint labels event
  have decoded' : setup.proposalRecoveryProposalOf (some sourceState) joint = some proposal := by
    simpa only [source] using decoded
  obtain ⟨owner, acting, notCommit, surviving, exposed, stored, address⟩ :=
    source_proposal_readback_origin setup image sourceState readback joint proposal decoded'
  by_cases semantic : OwnAction.disclosure ((event.joint owner).map (·.action)) = true
  · have read : NativeDisclosureReadback image 0 setup.program sourceState.point
        sourceState.excluded (proposalRecoveryJoint joint) := by
      simpa only [joint, setup.proposalRecoveryLiftJoint_semantic] using disclosure
    have disclosed : OwnAction.disclosure
        (((proposalRecoveryJoint joint) owner).map (·.action)) = true := by
      have same := setup.proposalRecoveryLiftJoint_semantic labels event
      change proposalRecoveryJoint joint = event.joint at same
      rw [same]
      exact semantic
    obtain ⟨actual, selected, archived⟩ := source_replay_disclosure_in_archive setup mode runtime
      leaks bounds plan maximal ordered inputs horizon scheduler current trace phase installed
      kind image origins kept sourceState readback joint read owner acting surviving notCommit
      generation lower upper disclosed
    have same := Option.some.inj (decoded'.symm.trans selected)
    exact same.symm ▸ archived
  · have silent := Bool.eq_false_of_not_eq_true semantic
    have requested := liftJoint_requested_of_no_disclosure setup labels event owner silent exposed
    obtain ⟨actual, archived, actualAddress⟩ :=
      (nativeArchiveLabels_some setup archive event owner sourceState source).mp requested
    let rank := instructionCount setup.program - ProtocolState.remaining setup.program
      sourceState.point
    have bounded : rank < ((toEventGraph setup.program).withMode mode).order.eventCount :=
      lt_of_lt_of_le upper phase.bounded
    let nativeEvent : ((toEventGraph setup.program).withMode mode).EventId := ⟨rank, bounded⟩
    have inside : nativeEvent ∈ phase.events := (phase.mem_events nativeEvent).mpr ⟨lower, upper⟩
    let initial := inputs.map (PhaseRuntimeState.initial plan)
    have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
      initial horizon scheduler trace
    have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler rawTrace
    have member := suffix.subset (List.mem_of_mem_head? installed)
    have low : current.execution.application.attempt.phase = phase.low := by
      simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
    have static := publicationBlockLow_of_phase setup.program mode plan maximal phase member kind
      nativeEvent inside
    have literal : actual.address =
        PhaseProposal.sourceAddress ⟨current.execution.application.attempt, nativeEvent⟩ := by
      have phaseAddress : setup.program.publicationBlockLow rank =
          current.execution.application.attempt.phase := static.trans low.symm
      change actual.address = ⟨setup.program.publicationBlockLow rank,
        sourceState.generation, rank⟩ at actualAddress
      change actual.address = ⟨current.execution.application.attempt.phase,
        current.execution.application.attempt.generation, rank⟩
      rw [phaseAddress, generation] at actualAddress
      exact actualAddress
    have value := PhaseProposal.archived_proposal_image_value runtime leaks bounds plan ordered
      inputs horizon scheduler current trace actual archived nativeEvent literal image kept
    have rankEq : proposal.address.event = nativeEvent.val := by
      exact congrArg ProposalRecoveryAddress.event address
    have sameValue : (⟨proposal.payload, proposal.value⟩ : Sigma L.Val) =
        ⟨actual.payload, actual.value⟩ := by
      rw [rankEq] at stored
      exact Option.some.inj (stored.symm.trans value)
    have same := typedProposal_ext proposal actual (address.trans actualAddress.symm) sameValue
    exact same.symm ▸ archived

end Vegas
