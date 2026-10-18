/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoverySplice
import Vegas.Game.CommitRecoveryHybridHistory

/-! # Legal proposal-labeled owner substitutions on the original source kernel -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

omit [IExpr.ResultTypes L] in
theorem proposalRecoveryJoint_update (focal : Player)
    (left right : Player → Option (ProposalRecoveryMove Player L)) :
    proposalRecoveryJoint (Function.update right focal (left focal)) =
      Function.update (proposalRecoveryJoint right) focal (proposalRecoveryJoint left focal) := by
  funext who
  by_cases own : who = focal
  · subst who
    simp only [proposalRecoveryJoint, Function.update_self]
  · simp only [proposalRecoveryJoint, Function.update_of_ne own]

theorem proposalRecovery_splice_joint_legal (focal : Player)
    (mine others : CommitRecoveryState setup.program) (metadata : mine.MetadataEq others)
    (before : ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program mine.point) =
      ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program others.point))
    (left right : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal (some mine) left)
    (rightLegal : setup.proposalRecoveryProtocol.Legal (some others) right) :
    setup.proposalRecoveryProtocol.Legal (some (CommitRecoveryState.splice focal mine others))
      (Function.update right focal (left focal)) := by
  have semantic := setup.commitRecovery_splice_joint_legal focal mine others metadata before
    (proposalRecoveryJoint left) (proposalRecoveryJoint right)
    (setup.proposalRecovery_erase_legal left leftLegal)
    (setup.proposalRecovery_erase_legal right rightLegal)
  rw [← proposalRecoveryJoint_update] at semantic
  refine ⟨semantic.1, ?_⟩
  intro who
  have offered := semantic.2 who
  have valid : ∀ move, Function.update right focal (left focal) who = some move → move.Valid := by
    intro move selected
    by_cases own : who = focal
    · subst who
      rw [Function.update_self] at selected
      have original := leftLegal.2 focal
      rw [selected] at original
      exact original.2.2
    · rw [Function.update_of_ne own] at selected
      have original := rightLegal.2 who
      rw [selected] at original
      exact original.2.2
  cases selected : Function.update right focal (left focal) who with
  | none =>
      change ¬ setup.commitRecoveryProtocol.active
        (some (CommitRecoveryState.splice focal mine others)) who
      simpa only [proposalRecoveryJoint, selected, Option.map_none] using offered
  | some move =>
      simp only [proposalRecoveryJoint, selected, Option.map_some] at offered
      exact ⟨offered.1, offered.2, valid move selected⟩

theorem proposalRecovery_step_splice_support (focal : Player)
    (mine others : CommitRecoveryState setup.program)
    (mineTrace : setup.proposalRecoveryProtocol.Trace (some mine))
    (metadata : mine.MetadataEq others)
    (before : ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program mine.point) =
      ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program others.point))
    (left right : Player → Option (ProposalRecoveryMove Player L))
    (leftNext rightNext : CommitRecoveryState setup.program)
    (leftSupport : leftNext ∈ (mine.step (proposalRecoveryJoint left)).support)
    (rightSupport : rightNext ∈ (others.step (proposalRecoveryJoint right)).support)
    (publicNext : setup.attemptPublicSignal focal (some leftNext) =
      setup.attemptPublicSignal focal (some rightNext)) :
    CommitRecoveryState.splice focal leftNext rightNext ∈
      ((CommitRecoveryState.splice focal mine others).step
        (proposalRecoveryJoint (Function.update right focal (left focal)))).support := by
  rw [proposalRecoveryJoint_update]
  exact setup.commitRecovery_step_splice_support focal mine others
    (setup.proposalRecoveryEraseTrace mineTrace) metadata before
    (proposalRecoveryJoint left) (proposalRecoveryJoint right) leftNext rightNext
    leftSupport rightSupport publicNext

end Vegas.SourceProgram.Setup
