/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryInformationReadback
import Vegas.Source.ProposalRecoveryTraceReadback

/-! # Complete labeled own coordinates and exact enriched history identity -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryJointRecall_actions (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryModel.infoOf who trace).2.map Prod.snd =
      (setup.proposalRecoveryJointRecall trace).filterMap (fun joint => joint who) := by
  change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who trace).2.map Prod.snd = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      rw [InfoSignals.ownPlay_extend]
      cases selected : joint who with
      | none =>
          simpa only [proposalRecoveryJointRecall, List.filterMap_cons, selected] using ih
      | some move =>
          simpa only [proposalRecoveryJointRecall, List.filterMap_cons, selected,
            List.map_cons] using congrArg (List.cons move) ih

private theorem option_word_eq {α β : Type} (read : α → β)
    (left right : List (Option α))
    (mask : left.map (Option.map read) = right.map (Option.map read))
    (actions : left.filterMap id = right.filterMap id) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons value rest => cases mask
  | cons value rest ih =>
      cases right with
      | nil => cases mask
      | cons other remaining =>
          have parts := List.cons.inj mask
          cases value <;> cases other
          · exact congrArg (List.cons none) (ih remaining parts.2 actions)
          · cases parts.1
          · cases parts.1
          · have picked := List.cons.inj actions
            exact congrArg₂ List.cons (congrArg some picked.1)
              (ih remaining parts.2 picked.2)

/-- Old semantic coordinates fix inactive positions; the literal enriched
own-action record supplies every additional disclosure label. -/
theorem proposalRecovery_coordinate_eq_of_info_eq (who : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (same : setup.proposalRecoveryModel.infoOf who left =
      setup.proposalRecoveryModel.infoOf who right) :
    (setup.proposalRecoveryJointRecall left).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall right).map (fun joint => joint who) := by
  have erased := congrArg (setup.proposalRecoveryEraseInfo who) same
  rw [setup.proposalRecoveryEraseInfo_observed,
    setup.proposalRecoveryEraseInfo_observed] at erased
  have semantic := setup.commitRecovery_coordinate_eq_of_info_eq who
    (setup.proposalRecoveryEraseTrace left) (setup.proposalRecoveryEraseTrace right) erased
  have actions := congrArg (fun info => info.2.map Prod.snd) same
  rw [setup.proposalRecoveryJointRecall_actions,
    setup.proposalRecoveryJointRecall_actions] at actions
  apply option_word_eq ProposalRecoveryMove.semantic
  · simpa only [List.map_map, proposalRecoveryJoint, Function.comp_def,
      ← setup.proposalRecoveryJointRecall_semantic] using semantic
  · simpa only [List.filterMap_map, Function.comp_def, id_eq] using actions

end Vegas.SourceProgram.Setup
