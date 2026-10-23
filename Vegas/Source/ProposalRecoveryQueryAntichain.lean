/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryProjection
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Archive-refined normalized queries preserve the original logical depth -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryQuery_word_length (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    (setup.proposalRecoveryQuery who information).1.1.2.length =
      information.1.2.length := by
  dsimp only [proposalRecoveryQuery]
  rw [setup.commitRecoveryNoMissInformation_erased_word_length]
  exact List.length_map _

theorem proposalRecoveryModel_word_length (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryModel.infoOf who trace).1.2.length = trace.length := by
  change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who trace).1.2.length = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih => exact congrArg Nat.succ ih

theorem proposalRecoveryQuery_trace_length (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace)).1.1.2.length =
      trace.length :=
  (setup.proposalRecoveryQuery_word_length who _).trans
    (setup.proposalRecoveryModel_word_length who trace)

end Vegas.SourceProgram.Setup
