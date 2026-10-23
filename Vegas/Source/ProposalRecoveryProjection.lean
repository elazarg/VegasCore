/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryInformation
import Vegas.Source.CommitRecoveryNoMissRepresentative

/-! # Semantic information projection and archive-refined source keys -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoveryEraseSignal (who : Player)
    (signal : setup.ProtocolView who ×
      ((Finset Player × Nat × Nat) × Option (ProposalRecoveryProposal L))) :
    setup.ProtocolView who × (Finset Player × Nat × Nat) :=
  (signal.1, signal.2.1)

def proposalRecoveryEraseBaseInfo (who : Player)
    (information : setup.proposalRecoverySignals.InfoState who) :
    setup.commitRecoverySignals.InfoState who :=
  (setup.proposalRecoveryEraseSignal who information.1,
    information.2.map (setup.proposalRecoveryEraseSignal who))

def proposalRecoveryEraseInfo (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.InfoState who :=
  (setup.proposalRecoveryEraseBaseInfo who information.1,
    information.2.map fun record =>
      (setup.proposalRecoveryEraseBaseInfo who record.1, record.2.semantic))

theorem proposalRecoveryEraseBaseInfo_observed (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    setup.proposalRecoveryEraseBaseInfo who (setup.proposalRecoverySignals.infoOf who trace) =
      setup.commitRecoverySignals.infoOf who (setup.proposalRecoveryEraseTrace trace) := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      change ((setup.commitRecoveryPrivate who _, setup.commitRecoveryPublic _),
          setup.proposalRecoveryEraseSignal who
              (setup.proposalRecoverySignals.infoOf who prior).1 ::
            (setup.proposalRecoverySignals.infoOf who prior).2.map
              (setup.proposalRecoveryEraseSignal who)) =
        ((setup.commitRecoveryPrivate who _, setup.commitRecoveryPublic _),
          (setup.commitRecoverySignals.infoOf who
              (setup.proposalRecoveryEraseTrace prior)).1 ::
            (setup.commitRecoverySignals.infoOf who
              (setup.proposalRecoveryEraseTrace prior)).2)
      exact congrArg (fun information =>
        ((setup.commitRecoveryPrivate who _, setup.commitRecoveryPublic _),
          information.1 :: information.2)) ih

theorem proposalRecoveryEraseOwnPlay (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoverySignals.ownPlay who trace).map
        (fun record => (setup.proposalRecoveryEraseBaseInfo who record.1, record.2.semantic)) =
      setup.commitRecoverySignals.ownPlay who (setup.proposalRecoveryEraseTrace trace) := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      rw [proposalRecoveryEraseTrace, InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend]
      cases selected : joint who with
      | none => simpa only [proposalRecoveryJoint, selected, Option.map_none] using ih
      | some move =>
          simp only [proposalRecoveryJoint, selected, Option.map_some, List.map_cons,
            setup.proposalRecoveryEraseBaseInfo_observed, ih]

theorem proposalRecoveryEraseInfo_observed (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    setup.proposalRecoveryEraseInfo who (setup.proposalRecoveryModel.infoOf who trace) =
      setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace trace) := by
  change setup.proposalRecoveryEraseInfo who
      (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who trace) =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
      (setup.proposalRecoveryEraseTrace trace)
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf]
  exact Prod.ext (setup.proposalRecoveryEraseBaseInfo_observed who trace)
    (setup.proposalRecoveryEraseOwnPlay who trace)

/-- Old full failure/address controls and the canonical proposal archive are
both retained. This key definition alone asserts no conditional-belief law. -/
def proposalRecoveryQuery (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.InfoState who × Finset (ProposalRecoveryProposal L) :=
  (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who
        (setup.proposalRecoveryEraseInfo who information)),
    setup.proposalRecoveryArchive who information)

end Vegas.SourceProgram.Setup
