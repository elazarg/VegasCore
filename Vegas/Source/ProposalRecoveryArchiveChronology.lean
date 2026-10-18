/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryArchiveLookup

/-! # Canonical archives recover proposal chronology on actual source paths -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryProposalOf_some_of_archive_cursor (who : Player)
    {leftSource leftTarget rightSource rightTarget : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftSource)
    (right : setup.proposalRecoveryProtocol.Trace rightSource)
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal leftSource leftJoint)
    (rightLegal : setup.proposalRecoveryProtocol.Legal rightSource rightJoint)
    (leftSupport : leftTarget ∈
      (setup.proposalRecoveryProtocol.step leftSource ⟨leftJoint, leftLegal⟩).support)
    (rightSupport : rightTarget ∈
      (setup.proposalRecoveryProtocol.step rightSource ⟨rightJoint, rightLegal⟩).support)
    (cursor : setup.proposalRecoveryCursor leftSource = setup.proposalRecoveryCursor rightSource)
    (archive : setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (left.extend leftJoint leftLegal leftSupport)) =
      setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (right.extend rightJoint rightLegal rightSupport)))
    (proposal : ProposalRecoveryProposal L)
    (decoded : setup.proposalRecoveryProposalOf leftSource leftJoint = some proposal) :
    setup.proposalRecoveryProposalOf rightSource rightJoint = some proposal := by
  have current : proposal ∈ setup.proposalRecoveryArchive who
      (setup.proposalRecoveryModel.infoOf who
        (left.extend leftJoint leftLegal leftSupport)) := by
    rw [setup.proposalRecoveryArchive_extend, decoded]
    exact Finset.mem_union_right _ (by simp)
  rw [archive, setup.proposalRecoveryArchive_extend] at current
  rcases Finset.mem_union.mp current with previous | current
  · exact False.elim ((setup.proposalRecovery_archive_cursor_fresh who right proposal previous)
      ((setup.proposalRecoveryProposalOf_cursor leftSource leftJoint proposal decoded).trans
        cursor))
  · have listed : proposal ∈ (setup.proposalRecoveryProposalOf rightSource rightJoint).toList :=
      List.mem_toFinset.mp current
    cases selected : setup.proposalRecoveryProposalOf rightSource rightJoint with
    | none => simp only [selected, Option.toList_none, List.not_mem_nil] at listed
    | some value =>
        have same : proposal = value := by
          simpa only [selected, Option.toList_some, List.mem_singleton] using listed
        exact congrArg some same.symm

theorem proposalRecoveryProposalOf_eq_of_archive_cursor (who : Player)
    {leftSource leftTarget rightSource rightTarget : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftSource)
    (right : setup.proposalRecoveryProtocol.Trace rightSource)
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal leftSource leftJoint)
    (rightLegal : setup.proposalRecoveryProtocol.Legal rightSource rightJoint)
    (leftSupport : leftTarget ∈
      (setup.proposalRecoveryProtocol.step leftSource ⟨leftJoint, leftLegal⟩).support)
    (rightSupport : rightTarget ∈
      (setup.proposalRecoveryProtocol.step rightSource ⟨rightJoint, rightLegal⟩).support)
    (cursor : setup.proposalRecoveryCursor leftSource = setup.proposalRecoveryCursor rightSource)
    (archive : setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (left.extend leftJoint leftLegal leftSupport)) =
      setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who
          (right.extend rightJoint rightLegal rightSupport))) :
    setup.proposalRecoveryProposalOf leftSource leftJoint =
      setup.proposalRecoveryProposalOf rightSource rightJoint := by
  cases chosen : setup.proposalRecoveryProposalOf leftSource leftJoint with
  | some proposal =>
      exact (setup.proposalRecoveryProposalOf_some_of_archive_cursor who left right
        leftJoint rightJoint leftLegal rightLegal leftSupport rightSupport cursor archive
        proposal chosen).symm
  | none =>
      cases other : setup.proposalRecoveryProposalOf rightSource rightJoint with
      | none => rfl
      | some proposal =>
          have impossible := setup.proposalRecoveryProposalOf_some_of_archive_cursor who right left
            rightJoint leftJoint rightLegal leftLegal rightSupport leftSupport
            cursor.symm archive.symm
            proposal other
          rw [chosen] at impossible
          cases impossible

theorem proposalRecoveryArchive_before_eq_erase_after (who : Player)
    {before after : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (proposal : ProposalRecoveryProposal L)
    (decoded : setup.proposalRecoveryProposalOf before joint = some proposal) :
    setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who prior) =
      (setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who
        (prior.extend joint legal supported))).erase proposal := by
  have absent : proposal ∉ setup.proposalRecoveryArchive who
      (setup.proposalRecoveryModel.infoOf who prior) := by
    intro present
    exact (setup.proposalRecovery_archive_cursor_fresh who prior proposal present)
      (setup.proposalRecoveryProposalOf_cursor before joint proposal decoded)
  rw [setup.proposalRecoveryArchive_extend, decoded]
  ext value
  simp only [Option.toList_some, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_erase, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
  constructor
  · intro member
    exact ⟨fun same => absent (same ▸ member), Or.inl member⟩
  · rintro ⟨different, member | same⟩
    · exact member
    · exact False.elim (different same)

theorem proposalRecoveryCursorWord_length
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryCursorWord trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih => exact congrArg Nat.succ ih

/-- The canonical archive and original cursor word determine EVERY proposal
delta, including the silent coordinates. No reach or strategy hypothesis is used. -/
theorem proposalRecoveryDeltaRecall_eq_of_archive_cursor_word (who : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (cursors : setup.proposalRecoveryCursorWord left = setup.proposalRecoveryCursorWord right)
    (archive : setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who left) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who right)) :
    setup.proposalRecoveryDeltaRecall left = setup.proposalRecoveryDeltaRecall right := by
  have clock : left.length = right.length := by
    have sizes := congrArg List.length cursors
    simpa only [setup.proposalRecoveryCursorWord_length] using sizes
  induction left generalizing rightState with
  | start =>
      cases right with
      | start => rfl
      | extend prior joint legal supported => simp only [Trace.length] at clock; omega
  | @extend leftSource leftTarget leftPrior leftJoint leftLegal leftSupport ih =>
      cases right with
      | start => simp only [Trace.length] at clock; omega
      | @extend rightSource rightTarget rightPrior rightJoint rightLegal rightSupport =>
          have cursorPair := List.cons.inj cursors
          have delta := setup.proposalRecoveryProposalOf_eq_of_archive_cursor who
            leftPrior rightPrior
            leftJoint rightJoint leftLegal rightLegal leftSupport rightSupport cursorPair.1 archive
          have before : setup.proposalRecoveryArchive who
              (setup.proposalRecoveryModel.infoOf who leftPrior) =
            setup.proposalRecoveryArchive who
              (setup.proposalRecoveryModel.infoOf who rightPrior) := by
            cases chosen : setup.proposalRecoveryProposalOf leftSource leftJoint with
            | none =>
                have other := chosen.symm.trans delta
                simpa only [setup.proposalRecoveryArchive_extend, chosen, ← other,
                  Option.toList_none, List.toFinset_nil, Finset.union_empty] using archive
            | some proposal =>
                have other := delta.symm.trans chosen
                rw [setup.proposalRecoveryArchive_before_eq_erase_after who leftPrior leftJoint
                  leftLegal leftSupport proposal chosen,
                  setup.proposalRecoveryArchive_before_eq_erase_after who rightPrior rightJoint
                    rightLegal rightSupport proposal other, archive]
          have previousClock : leftPrior.length = rightPrior.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          exact congrArg₂ List.cons delta
            (ih rightPrior cursorPair.2 before previousClock)

end Vegas.SourceProgram.Setup
