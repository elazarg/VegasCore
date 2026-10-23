/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryHybridDisclosure
import Vegas.Source.ProposalRecoverySupportSplice

/-! # Whole proposal words on genuine owner-coordinate hybrid histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryDeltaRecall_eq_of_split_information (focal : Player)
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
    (coordinates : ∀ who,
      (setup.proposalRecoveryJointRecall hybrid).map (fun joint => joint who) =
        if who = focal then (setup.proposalRecoveryJointRecall mine).map (fun joint => joint who)
        else (setup.proposalRecoveryJointRecall others).map (fun joint => joint who))
    (delta : setup.proposalRecoveryDeltaRecall mine = setup.proposalRecoveryDeltaRecall others) :
    setup.proposalRecoveryDeltaRecall hybrid = setup.proposalRecoveryDeltaRecall others := by
  induction hybrid generalizing mineState othersState with
  | start =>
      have sizes := congrArg List.length publicHybrid
      simp only [setup.publicRecall_length, setup.proposalRecoveryEraseTrace_length,
        Trace.length] at sizes
      cases others with
      | start => rfl
      | extend prior joint legal supported => simp only [Trace.length] at sizes; omega
  | @extend hybridSource hybridTarget hybridPrior hybridJoint hybridLegal hybridSupport ih =>
      cases others with
      | start =>
          have sizes := congrArg List.length publicHybrid
          simp only [setup.publicRecall_length, setup.proposalRecoveryEraseTrace_length,
            Trace.length] at sizes
          omega
      | @extend othersSource othersTarget othersPrior othersJoint othersLegal othersSupport =>
          cases mine with
          | start =>
              have sizes := congrArg List.length publicMine
              simp only [setup.publicRecall_length, setup.proposalRecoveryEraseTrace_length,
                Trace.length] at sizes
              omega
          | @extend mineSource mineTarget minePrior mineJoint mineLegal mineSupport =>
              have minePublic := List.cons.inj (by
                simpa only [proposalRecoveryEraseTrace, setup.publicRecall_extend] using publicMine)
              have hybridPublic := List.cons.inj (by
                simpa only [proposalRecoveryEraseTrace, setup.publicRecall_extend]
                  using publicHybrid)
              have previous who :
                  setup.commitRecoveryModel.infoOf who
                      (setup.proposalRecoveryEraseTrace hybridPrior) =
                    if who = focal then setup.commitRecoveryModel.infoOf who
                      (setup.proposalRecoveryEraseTrace minePrior)
                    else setup.commitRecoveryModel.infoOf who
                      (setup.proposalRecoveryEraseTrace othersPrior) := by
                by_cases own : who = focal
                · simp only [own, ite_true]
                  exact setup.commitRecovery_predecessor_information_eq who
                    (setup.proposalRecoveryEraseTrace hybridPrior)
                    (setup.proposalRecoveryEraseTrace minePrior)
                    (proposalRecoveryJoint hybridJoint) (proposalRecoveryJoint mineJoint)
                    (setup.proposalRecovery_erase_legal hybridJoint hybridLegal)
                    (setup.proposalRecovery_erase_legal mineJoint mineLegal)
                    hybridSupport mineSupport (by
                      simpa only [proposalRecoveryEraseTrace, own, ite_true] using information who)
                · simp only [own, ite_false]
                  exact setup.commitRecovery_predecessor_information_eq who
                    (setup.proposalRecoveryEraseTrace hybridPrior)
                    (setup.proposalRecoveryEraseTrace othersPrior)
                    (proposalRecoveryJoint hybridJoint) (proposalRecoveryJoint othersJoint)
                    (setup.proposalRecovery_erase_legal hybridJoint hybridLegal)
                    (setup.proposalRecovery_erase_legal othersJoint othersLegal)
                    hybridSupport othersSupport (by
                      simpa only [proposalRecoveryEraseTrace, own, ite_false] using information who)
              have choices who : hybridJoint who =
                  if who = focal then mineJoint who else othersJoint who := by
                by_cases own : who = focal
                · subst who
                  exact (List.cons.inj (by
                    simpa only [proposalRecoveryJointRecall, List.map_cons, ite_true]
                      using coordinates focal)).1
                · simpa only [own, ite_false] using (List.cons.inj (by
                    simpa only [proposalRecoveryJointRecall, List.map_cons, own, ite_false]
                      using coordinates who)).1
              have previousCoordinates who :
                  (setup.proposalRecoveryJointRecall hybridPrior).map (fun joint => joint who) =
                    if who = focal then
                      (setup.proposalRecoveryJointRecall minePrior).map (fun joint => joint who)
                    else (setup.proposalRecoveryJointRecall othersPrior).map
                      (fun joint => joint who) := by
                by_cases own : who = focal
                · subst who
                  exact (List.cons.inj (by
                    simpa only [proposalRecoveryJointRecall, List.map_cons, ite_true]
                      using coordinates focal)).2
                · simpa only [own, ite_false] using (List.cons.inj (by
                    simpa only [proposalRecoveryJointRecall, List.map_cons, own, ite_false]
                      using coordinates who)).2
              have deltas := List.cons.inj delta
              have current := setup.proposalRecoveryProposalOf_eq_of_split_information focal
                minePrior othersPrior hybridPrior minePublic.2 hybridPublic.2 previous
                mineJoint othersJoint hybridJoint choices deltas.1
              exact congrArg₂ List.cons current
                (ih minePrior othersPrior minePublic.2 hybridPublic.2 previous
                  previousCoordinates deltas.2)

end Vegas.SourceProgram.Setup
