/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryRank
import Vegas.Source.ProposalRecoveryInformation
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Actual proposal addresses identify unique source prefixes -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryProposalOf_some_rank (current : CommitRecoveryState setup.program)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (proposal : ProposalRecoveryProposal L)
    (decoded : setup.proposalRecoveryProposalOf (some current) joint = some proposal) :
    proposal.address.generation = current.generation ∧
      proposal.address.event = instructionCount setup.program -
        ProtocolState.remaining setup.program current.point := by
  change Option.map _ (ProtocolState.recoveryProposal setup.program current.point
    (fun who => if who ∈ current.excluded then none else joint who)) = some proposal at decoded
  obtain ⟨pair, original, same⟩ := Option.map_eq_some_iff.mp decoded
  have ranked := ProtocolState.recoveryProposal_rank setup.program current.point _
    pair.1 pair.2 original
  exact ⟨(congrArg (fun value => value.address.generation) same).symm,
    (congrArg (fun value => value.address.event) same).symm.trans ranked⟩

theorem proposalRecoveryEraseTrace_prefix
    {first last : setup.proposalRecoveryProtocol.State}
    {before : setup.proposalRecoveryProtocol.Trace first}
    {after : setup.proposalRecoveryProtocol.Trace last} (kept : TracePrefix before after) :
    TracePrefix (setup.proposalRecoveryEraseTrace before)
      (setup.proposalRecoveryEraseTrace after) := by
  induction kept with
  | refl => exact .refl
  | extend earlier joint legal supported ih =>
      exact .extend ih (proposalRecoveryJoint joint)
        (setup.proposalRecovery_erase_legal joint legal) supported

theorem proposalRecovery_proposal_word_origin (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (proposal : ProposalRecoveryProposal L)
    (member : proposal ∈ setup.proposalRecoveryProposalWord who
      (setup.proposalRecoveryModel.infoOf who trace)) :
    ∃ (before after : setup.proposalRecoveryProtocol.State)
      (prior : setup.proposalRecoveryProtocol.Trace before)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before joint)
      (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal supported) trace ∧
      setup.proposalRecoveryProposalOf before joint = some proposal := by
  induction trace with
  | start => cases member
  | @extend before after prior joint legal supported ih =>
      rw [setup.proposalRecoveryProposalWord_extend] at member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨source, target, priorTrace, selected, allowed, reached, kept, decoded⟩ := ih earlier
        exact ⟨source, target, priorTrace, selected, allowed, reached,
          .extend kept joint legal supported, decoded⟩
      · have decoded : setup.proposalRecoveryProposalOf before joint = some proposal := by
          cases delta : setup.proposalRecoveryProposalOf before joint with
          | none => simp only [delta, Option.toList_none, List.not_mem_nil] at current
          | some value =>
              have same : proposal = value := by simpa only [delta, Option.toList_some,
                List.mem_singleton] using current
              exact congrArg some same.symm
        exact ⟨before, after, prior, joint, legal, supported, .refl, decoded⟩

end Vegas.SourceProgram.Setup
