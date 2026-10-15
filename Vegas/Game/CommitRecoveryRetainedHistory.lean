/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryRestriction
import Vegas.Source.CommitRecoveryClearSuccessor

/-! # Actual source projections at retained recovery information values -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Every history in the full retained information fiber is clear, including
histories with hidden foreign unusable bindings. No intended-state claim is
made about those hidden bindings. -/
theorem commitRecovery_retained_clear (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who)
    (history : setup.commitRecoveryModel.InformationHistory who
      (setup.commitRecoveryInformation wellFormed who view)) :
    setup.CommitRecoveryClear history.1.state := by
  have observed := congrArg
    (fun info : setup.commitRecoveryModel.InfoState who => info.1.1.2.1) history.2
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who history.1.trace).1.1.2.1 = _
    at observed
  rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current] at observed
  have excluded := setup.commitRecoveryRetainedInfo_excluded wellFormed who view
  change (setup.commitRecoveryPublic history.1.state).1 =
    (setup.commitRecoveryRetainedInfo wellFormed who view).1.2.1 at observed
  rw [excluded] at observed
  cases state : history.1.state with
  | none => trivial
  | some current =>
      simpa only [state, commitRecoveryPublic, CommitRecoveryClear, Option.elim_some] using observed

/-- Retained recovery fibers have actual original-source histories with the
same source view; the projection retains all effective source actions. -/
def commitRecoverySourceInformationHistory (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who)
    (history : setup.commitRecoveryModel.InformationHistory who
      (setup.commitRecoveryInformation wellFormed who view)) :
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).InformationHistory
      who view := by
  let clear := setup.commitRecovery_retained_clear wellFormed who view history
  refine ⟨setup.commitRecoveryClearHistory history.1 clear, ?_⟩
  change (setup.informationModel (CommitmentInterface.forfeiture setup.program)).infoOf who
    (setup.commitRecoveryClearTrace history.1.trace clear) = view
  rw [setup.commitRecoveryClearTrace_observe]
  have observed := congrArg
    (fun info : setup.commitRecoveryModel.InfoState who => info.1.1.1) history.2
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who history.1.trace).1.1.1 = _
    at observed
  rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current] at observed
  exact observed.trans (setup.commitRecoveryRetainedInfo_current wellFormed who view)

end Vegas.SourceProgram.Setup
