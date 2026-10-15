/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryClearRecall
import Vegas.Game.CommitRecoveryInformationEmbedding

/-! # Intended information at actual clear recovery histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- An actual clear history with an intended current source view realizes the
same complete embedded information, rather than merely its private projection. -/
theorem commitRecoveryInformation_of_clear (wellFormed : setup.WellFormed) (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state)
    (original : setup.intendedProtocol.History)
    (same : setup.commitRecoveryPrivate who state = setup.intendedModel.infoOf who original.trace) :
    setup.commitRecoveryModel.infoOf who trace =
      setup.commitRecoveryInformation wellFormed who
        (setup.intendedModel.infoOf who original.trace) := by
  rw [← setup.commitRecoveryInformation_observed wellFormed who original]
  apply setup.commitRecovery_clear_info_eq who trace
    (setup.commitRecoveryLiftHistory wellFormed original).trace clear
    (setup.commitRecoveryLiftHistory_clear wellFormed original)
  exact same.trans (setup.commitRecoveryLiftHistory_private wellFormed who original).symm

end Vegas.SourceProgram.Setup
