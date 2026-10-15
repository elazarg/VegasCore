/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryClearDecoder
import Vegas.Source.CommitRecoveryProjection

/-! # Genuine source history fibers of clear auxiliary information -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem commitRecovery_clearInformation_fiber_clear (wellFormed : setup.WellFormed)
    (who : Player) (view : setup.ProtocolView who)
    (history : setup.commitRecoveryModel.InformationHistory who
      (setup.commitRecoveryClearInformation wellFormed who view)) :
    setup.CommitRecoveryClear history.1.state := by
  have observed := congrArg
    (fun info : setup.commitRecoveryModel.InfoState who => info.1.1.2.1) history.2
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
    history.1.trace).1.1.2.1 = _ at observed
  rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current] at observed
  rw [setup.commitRecoveryClearInformation_excluded] at observed
  cases state : history.1.state with
  | none => trivial
  | some current =>
      simpa only [state, commitRecoveryPublic, CommitRecoveryClear, Option.elim_some]
        using observed

theorem commitRecovery_clearInformation_fiber_private (wellFormed : setup.WellFormed)
    (who : Player) (view : setup.ProtocolView who)
    (history : setup.commitRecoveryModel.InformationHistory who
      (setup.commitRecoveryClearInformation wellFormed who view)) :
    setup.commitRecoveryPrivate who history.1.state = view := by
  have observed := congrArg
    (fun info : setup.commitRecoveryModel.InfoState who => info.1.1.1) history.2
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
    history.1.trace).1.1.1 = _ at observed
  rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current] at observed
  exact observed.trans (setup.commitRecoveryClearInformation_current wellFormed who view)

/-- Every row of the complete auxiliary information fiber projects to a
genuine initialized source history with the exact same complete current view. -/
def commitRecoveryClearSourceInformationHistory (wellFormed : setup.WellFormed)
    (who : Player) (view : setup.ProtocolView who)
    (history : setup.commitRecoveryModel.InformationHistory who
      (setup.commitRecoveryClearInformation wellFormed who view)) :
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).InformationHistory
      who view := by
  let clear := setup.commitRecovery_clearInformation_fiber_clear wellFormed who view history
  refine ⟨setup.commitRecoveryClearHistory history.1 clear, ?_⟩
  change (setup.informationModel (CommitmentInterface.forfeiture setup.program)).infoOf who
    (setup.commitRecoveryClearTrace history.1.trace clear) = view
  rw [setup.commitRecoveryClearTrace_observe]
  exact setup.commitRecovery_clearInformation_fiber_private wellFormed who view history

/-- The entire clear information fiber has a common genuine source depth.
This includes rows whose hidden foreign commitment values or actions differ. -/
theorem commitRecovery_clearInformation_fiber_length (wellFormed : setup.WellFormed)
    (who : Player) (view : setup.ProtocolView who)
    (first second : setup.commitRecoveryModel.InformationHistory who
      (setup.commitRecoveryClearInformation wellFormed who view)) :
    first.1.trace.length = second.1.trace.length := by
  apply setup.commitRecoveryClearTrace_length_eq_of_private who first.1.trace second.1.trace
    (setup.commitRecovery_clearInformation_fiber_clear wellFormed who view first)
    (setup.commitRecovery_clearInformation_fiber_clear wellFormed who view second)
  exact (setup.commitRecovery_clearInformation_fiber_private wellFormed who view first).trans
    (setup.commitRecovery_clearInformation_fiber_private wellFormed who view second).symm

end Vegas.SourceProgram.Setup
