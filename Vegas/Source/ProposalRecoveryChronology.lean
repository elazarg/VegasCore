/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryRank
import Vegas.Source.ProposalRecoveryInformation
import Vegas.Source.CommitRecoveryCursor
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

/-- Equal actual proposal addresses on one source path identify the same
pre-step history, including all original private stores and chance outcomes. -/
theorem proposalRecovery_prefix_eq_of_same_proposal_address
    (first second : CommitRecoveryState setup.program)
    (left : setup.proposalRecoveryProtocol.Trace (some first))
    (right : setup.proposalRecoveryProtocol.Trace (some second)) (kept : TracePrefix left right)
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftProposal rightProposal : ProposalRecoveryProposal L)
    (leftDecoded : setup.proposalRecoveryProposalOf (some first) leftJoint = some leftProposal)
    (rightDecoded : setup.proposalRecoveryProposalOf (some second) rightJoint = some rightProposal)
    (address : leftProposal.address = rightProposal.address) :
    (⟨some first, left⟩ : setup.proposalRecoveryProtocol.History) = ⟨some second, right⟩ := by
  have leftRank := setup.proposalRecoveryProposalOf_some_rank first leftJoint leftProposal
    leftDecoded
  have rightRank := setup.proposalRecoveryProposalOf_some_rank second rightJoint rightProposal
    rightDecoded
  have generations : first.generation = second.generation :=
    leftRank.1.symm.trans ((congrArg ProposalRecoveryAddress.generation address).trans rightRank.1)
  have eventEq := congrArg ProposalRecoveryAddress.event address
  have leftBound := ProtocolState.remaining_le_instructionCount setup.program first.point
  have rightBound := ProtocolState.remaining_le_instructionCount setup.program second.point
  have remaining : ProtocolState.remaining setup.program first.point =
      ProtocolState.remaining setup.program second.point := by omega
  have oldKept := setup.proposalRecoveryEraseTrace_prefix kept
  have lengths := setup.commitRecovery_same_generation_length oldKept.reachesWithin
    first second rfl rfl generations
  rw [remaining, setup.proposalRecoveryEraseTrace_length,
    setup.proposalRecoveryEraseTrace_length] at lengths
  exact kept.eq_of_length (Nat.add_left_cancel lengths).symm

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

theorem proposalRecoveryProposalOf_fresh_address (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (proposal : ProposalRecoveryProposal L)
    (decoded : setup.proposalRecoveryProposalOf (some current) joint = some proposal) :
    proposal.address ∉
      (setup.proposalRecoveryProposalWord who (setup.proposalRecoveryModel.infoOf who trace)).map
        ProposalRecoveryProposal.address := by
  intro repeated
  obtain ⟨earlier, member, sameAddress⟩ := List.mem_map.mp repeated
  obtain ⟨before, after, prior, selected, legal, supported, kept, oldDecoded⟩ :=
    setup.proposalRecovery_proposal_word_origin who trace earlier member
  cases before with
  | none => cases oldDecoded
  | some before =>
      have priorKept : TracePrefix prior trace :=
        (TracePrefix.extend .refl selected legal supported).trans kept
      have equal := setup.proposalRecovery_prefix_eq_of_same_proposal_address
        before current prior trace priorKept selected joint earlier proposal oldDecoded decoded
        sameAddress
      have sameLength := congrArg (fun history => history.trace.length) equal
      change prior.length = trace.length at sameLength
      have shorter := kept.length_le
      simp only [Trace.length] at shorter
      omega

theorem proposalRecoveryProposalWord_addresses_nodup (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    ((setup.proposalRecoveryProposalWord who (setup.proposalRecoveryModel.infoOf who trace)).map
      ProposalRecoveryProposal.address).Nodup := by
  induction trace with
  | start => exact List.nodup_nil
  | @extend before after prior joint legal supported ih =>
      rw [setup.proposalRecoveryProposalWord_extend, List.map_append]
      cases before with
      | none => simpa only [proposalRecoveryProposalOf_initial, Option.toList_none,
          List.map_nil, List.append_nil] using ih
      | some before =>
          cases delta : setup.proposalRecoveryProposalOf (some before) joint with
          | none => simpa only [delta, Option.toList_none, List.map_nil, List.append_nil] using ih
          | some proposal =>
              have fresh := setup.proposalRecoveryProposalOf_fresh_address
                who before prior joint proposal delta
              simp only [Option.toList_some, List.map_cons, List.map_nil]
              exact List.nodup_append.mpr ⟨ih, List.nodup_singleton _, by
                intro address left other right
                have same : other = proposal.address := List.mem_singleton.mp right
                subst other
                intro equal
                subst address
                exact fresh left⟩

theorem proposalRecoveryArchive_eq_of_same_address (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (first second : ProposalRecoveryProposal L)
    (left : first ∈ setup.proposalRecoveryArchive who
      (setup.proposalRecoveryModel.infoOf who trace))
    (right : second ∈ setup.proposalRecoveryArchive who
      (setup.proposalRecoveryModel.infoOf who trace))
    (same : first.address = second.address) : first = second := by
  dsimp only [proposalRecoveryArchive] at left right
  exact List.inj_on_of_nodup_map
    (setup.proposalRecoveryProposalWord_addresses_nodup who trace)
    (List.mem_toFinset.mp left) (List.mem_toFinset.mp right) same

end Vegas.SourceProgram.Setup
