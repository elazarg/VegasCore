/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPublicHistory
import Vegas.Source.ProposalRecoveryWordLift
import Vegas.Source.ProposalRecoveryReadout
import Vegas.Game.CommitRecoveryAncillaryBelief

/-! # Full labeled information from actual semantic records and proposal chronology -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryProposalOf_eq_of_actor_information (who : Player)
    (first second : CommitRecoveryState setup.program)
    (leftTrace : setup.commitRecoveryProtocol.Trace (some first))
    (rightTrace : setup.commitRecoveryProtocol.Trace (some second))
    (active : ProtocolState.actor setup.program first.point = some who)
    (same : setup.commitRecoveryModel.infoOf who leftTrace =
      setup.commitRecoveryModel.infoOf who rightTrace)
    (left right : Player → Option (ProposalRecoveryMove Player L))
    (own : left who = right who) :
    setup.proposalRecoveryProposalOf (some first) left =
      setup.proposalRecoveryProposalOf (some second) right := by
  have observed := congrArg (fun information => information.1.1) same
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who leftTrace).1.1 =
    (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who rightTrace).1.1 at observed
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at observed
  rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at observed
  have viewEq : setup.commitRecoveryPrivate who (some first) =
      setup.commitRecoveryPrivate who (some second) := congrArg Prod.fst observed
  have publicEq := congrArg Prod.snd observed
  have excluded : first.excluded = second.excluded := congrArg Prod.fst publicEq
  have generation : first.generation = second.generation :=
    congrArg (fun publicView => publicView.2.1) publicEq
  exact setup.proposalRecoveryProposalOf_eq_of_actor_view who first second active
    viewEq excluded generation left right own

theorem commitRecovery_predecessor_information_eq (who : Player)
    {leftSource leftTarget rightSource rightTarget : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftSource)
    (right : setup.commitRecoveryProtocol.Trace rightSource)
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (leftLegal : setup.commitRecoveryProtocol.Legal leftSource leftJoint)
    (rightLegal : setup.commitRecoveryProtocol.Legal rightSource rightJoint)
    (leftSupport : leftTarget ∈
      (setup.commitRecoveryProtocol.step leftSource ⟨leftJoint, leftLegal⟩).support)
    (rightSupport : rightTarget ∈
      (setup.commitRecoveryProtocol.step rightSource ⟨rightJoint, rightLegal⟩).support)
    (same : setup.commitRecoveryModel.infoOf who (left.extend leftJoint leftLegal leftSupport) =
      setup.commitRecoveryModel.infoOf who (right.extend rightJoint rightLegal rightSupport)) :
    setup.commitRecoveryModel.infoOf who left = setup.commitRecoveryModel.infoOf who right := by
  have coordinates := setup.commitRecovery_coordinate_eq_of_info_eq who _ _ same
  have ownChoice : leftJoint who = rightJoint who := (List.cons.inj coordinates).1
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ at same ⊢
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at same ⊢
  have base := congrArg Prod.fst same
  have own := congrArg Prod.snd same
  rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend] at base
  have past := List.cons.inj (congrArg Prod.snd base)
  have beforeBase : setup.commitRecoverySignals.infoOf who left =
      setup.commitRecoverySignals.infoOf who right := Prod.ext past.1 past.2
  apply Prod.ext beforeBase
  rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend, ownChoice] at own
  dsimp only at own ⊢
  cases selected : rightJoint who with
  | none => simpa only [selected] using own
  | some _ =>
      simp only [selected] at own
      exact (List.cons.inj own).2

/-- Full old information, the actual full proposal chronology, and the raw
own labeled coordinate determine the full enriched information exactly. -/
theorem proposalRecovery_info_eq_of_semantic_public_coordinate (who : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (semantic : setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace left) =
      setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace right))
    (publicWord : setup.proposalRecoveryPublicRecall who left =
      setup.proposalRecoveryPublicRecall who right)
    (coordinate : (setup.proposalRecoveryJointRecall left).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall right).map (fun joint => joint who)) :
    setup.proposalRecoveryModel.infoOf who left = setup.proposalRecoveryModel.infoOf who right := by
  have clock : left.length = right.length := by
    have lengths := congrArg List.length publicWord
    simpa only [setup.proposalRecoveryPublicRecall_length, Nat.add_left_inj] using lengths
  induction left generalizing rightState with
  | start =>
      cases right with
      | start => rfl
      | extend prior joint legal supported => simp only [Trace.length] at clock; omega
  | @extend leftSource leftTarget leftPrior leftJoint leftLegal leftSupport ih =>
      cases right with
      | start => simp only [Trace.length] at clock; omega
      | @extend rightSource rightTarget rightPrior rightJoint rightLegal rightSupport =>
          have publicPair := List.cons.inj publicWord
          have coordinatePair := List.cons.inj coordinate
          have earlier := setup.commitRecovery_predecessor_information_eq who
            (setup.proposalRecoveryEraseTrace leftPrior)
            (setup.proposalRecoveryEraseTrace rightPrior)
            (proposalRecoveryJoint leftJoint) (proposalRecoveryJoint rightJoint)
            (setup.proposalRecovery_erase_legal leftJoint leftLegal)
            (setup.proposalRecovery_erase_legal rightJoint rightLegal)
            leftSupport rightSupport semantic
          have previousClock : leftPrior.length = rightPrior.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          have before := ih rightPrior earlier publicPair.2 coordinatePair.2 previousClock
          have semanticSignal := congrArg (fun information => information.1.1) semantic
          change (setup.commitRecoverySignals.infoOf who
              (setup.proposalRecoveryEraseTrace (leftPrior.extend leftJoint leftLegal
                leftSupport))).1 =
            (setup.commitRecoverySignals.infoOf who
              (setup.proposalRecoveryEraseTrace (rightPrior.extend rightJoint rightLegal
                rightSupport))).1 at semanticSignal
          rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current]
            at semanticSignal
          apply setup.proposalRecovery_information_extend_congr who leftPrior rightPrior
            leftJoint rightJoint leftLegal rightLegal leftSupport rightSupport before
            coordinatePair.1
          have viewEq : setup.commitRecoveryPrivate who leftTarget =
              setup.commitRecoveryPrivate who rightState := congrArg Prod.fst semanticSignal
          have controlEq : setup.commitRecoveryPublic leftTarget =
              setup.commitRecoveryPublic rightState := congrArg Prod.snd semanticSignal
          have deltaEq : setup.proposalRecoveryProposalOf leftSource leftJoint =
              setup.proposalRecoveryProposalOf rightSource rightJoint :=
            congrArg Prod.snd publicPair.1
          exact Prod.ext viewEq (Prod.ext controlEq deltaEq)

end Vegas.SourceProgram.Setup
