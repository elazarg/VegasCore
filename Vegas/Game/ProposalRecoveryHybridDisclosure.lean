/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryInformationReadback
import Vegas.Game.ProposalRecoveryArchivePublicHistory
import Vegas.Source.ProposalRecoveryWordSplice

/-! # Proposal disclosure under the original owner-coordinate history exchange -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem actor_eq_of_public (who : Player)
    (first second : setup.commitRecoveryProtocol.State)
    (same : setup.attemptPublicSignal who first = setup.attemptPublicSignal who second) :
    first.bind (fun current => ProtocolState.actor setup.program current.point) =
      second.bind (fun current => ProtocolState.actor setup.program current.point) := by
  have observed := congrArg
    (fun signal => signal.1.bind (ProtocolView.actor who setup.program)) same
  cases first <;> cases second
  all_goals first
    | rfl
    | simpa only [attemptPublicSignal, commitRecoveryPrivate, Option.map_none, Option.map_some,
      Option.bind_none, Option.bind_some, ProtocolView.actor_publicOnly,
      ProtocolState.actor_observe_eq] using observed

private theorem proposal_none_of_actor_none (state : setup.proposalRecoveryProtocol.State)
    (silent : state.bind (fun current => ProtocolState.actor setup.program current.point) = none)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryProposalOf state joint = none := by
  cases state with
  | none => rfl
  | some current =>
      have absent := ProtocolState.recoveryProposal_eq_none_of_actor_none
        setup.program current.point silent
        (fun who => if who ∈ current.excluded then none else joint who)
      simp only [proposalRecoveryProposalOf, Option.bind_some, absent, Option.map_none]

private theorem current_public_eq (who : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftState)
    (right : setup.commitRecoveryProtocol.Trace rightState)
    (same : setup.attemptPublicRecall who left = setup.attemptPublicRecall who right) :
    setup.attemptPublicSignal who leftState = setup.attemptPublicSignal who rightState := by
  have head := congrArg List.head? same
  simpa only [attemptPublicRecall, List.map_cons, List.head?_cons,
    setup.commitRecoverySignals_current, attemptPublicSignal, Option.some.injEq] using head

theorem proposalRecoveryProposalOf_eq_of_split_information (focal : Player)
    {mineState othersState hybridState : setup.proposalRecoveryProtocol.State}
    (mine : setup.proposalRecoveryProtocol.Trace mineState)
    (others : setup.proposalRecoveryProtocol.Trace othersState)
    (hybrid : setup.proposalRecoveryProtocol.Trace hybridState)
    (publicMine : setup.attemptPublicRecall focal (setup.proposalRecoveryEraseTrace mine) =
      setup.attemptPublicRecall focal (setup.proposalRecoveryEraseTrace others))
    (publicHybrid : setup.attemptPublicRecall focal (setup.proposalRecoveryEraseTrace hybrid) =
      setup.attemptPublicRecall focal (setup.proposalRecoveryEraseTrace others))
    (information : ∀ who,
      setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace hybrid) =
        if who = focal then
          setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace mine)
        else setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace others))
    (mineJoint othersJoint hybridJoint : Player → Option (ProposalRecoveryMove Player L))
    (coordinates : ∀ who, hybridJoint who =
      if who = focal then mineJoint who else othersJoint who)
    (delta : setup.proposalRecoveryProposalOf mineState mineJoint =
      setup.proposalRecoveryProposalOf othersState othersJoint) :
    setup.proposalRecoveryProposalOf hybridState hybridJoint =
      setup.proposalRecoveryProposalOf othersState othersJoint := by
  have mineActor := setup.actor_eq_of_public focal mineState othersState
    (setup.current_public_eq focal _ _ publicMine)
  have hybridActor := setup.actor_eq_of_public focal hybridState othersState
    (setup.current_public_eq focal _ _ publicHybrid)
  cases selected : othersState.bind
      (fun current => ProtocolState.actor setup.program current.point) with
  | none =>
      rw [setup.proposal_none_of_actor_none hybridState (hybridActor.trans selected),
        setup.proposal_none_of_actor_none othersState selected]
  | some who =>
      cases hybridState with
      | none => simp only [Option.bind_none, selected, reduceCtorEq] at hybridActor
      | some current =>
          have active : ProtocolState.actor setup.program current.point = some who :=
            hybridActor.trans selected
          by_cases own : who = focal
          · cases mineState with
            | none => simp only [Option.bind_none, selected, reduceCtorEq] at mineActor
            | some original =>
                have result := setup.proposalRecoveryProposalOf_eq_of_actor_information who
                  current original (setup.proposalRecoveryEraseTrace hybrid)
                  (setup.proposalRecoveryEraseTrace mine) active
                  (by simpa only [own, ite_true] using information who)
                  hybridJoint mineJoint (by simpa only [own, ite_true] using coordinates who)
                exact result.trans delta
          · cases othersState with
            | none => cases selected
            | some original =>
                exact setup.proposalRecoveryProposalOf_eq_of_actor_information who
                  current original (setup.proposalRecoveryEraseTrace hybrid)
                  (setup.proposalRecoveryEraseTrace others) active
                  (by simpa only [own, ite_false] using information who)
                  hybridJoint othersJoint (by simpa only [own, ite_false] using coordinates who)

end Vegas.SourceProgram.Setup
