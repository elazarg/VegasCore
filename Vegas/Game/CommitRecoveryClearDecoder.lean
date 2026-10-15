/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryClearInformation

/-! # Complete auxiliary information decoded from realized clear source views -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Realized clear views select a genuine complete auxiliary information value.
The intended injection supplies the total extension at unrealized views. -/
def commitRecoveryClearInformation (wellFormed : setup.WellFormed) (who : Player) :
    setup.ProtocolView who → setup.commitRecoveryModel.InfoState who := by
  classical
  exact fun view => if witness : ∃ history : setup.commitRecoveryProtocol.History,
      setup.CommitRecoveryClear history.state ∧
        setup.commitRecoveryPrivate who history.state = view then
    setup.commitRecoveryModel.infoOf who witness.choose.trace
  else setup.commitRecoveryInformation wellFormed who view

theorem commitRecoveryClearInformation_current (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who) :
    (setup.commitRecoveryClearInformation wellFormed who view).1.1.1 = view := by
  classical
  unfold commitRecoveryClearInformation
  split
  · next witness =>
      change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
        witness.choose.trace).1.1.1 = _
      rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]
      exact witness.choose_spec.2
  · exact setup.commitRecoveryRetainedInfo_current wellFormed who view

theorem commitRecoveryClearInformation_injective (wellFormed : setup.WellFormed) (who : Player) :
    Function.Injective (setup.commitRecoveryClearInformation wellFormed who) := by
  intro first second same
  simpa only [setup.commitRecoveryClearInformation_current] using
    congrArg (fun info : setup.commitRecoveryModel.InfoState who => info.1.1.1) same

theorem commitRecoveryClearInformation_excluded (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who) :
    (setup.commitRecoveryClearInformation wellFormed who view).1.1.2.1 = ∅ := by
  classical
  unfold commitRecoveryClearInformation
  split
  · next witness =>
      change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
        witness.choose.trace).1.1.2.1 = _
      rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]
      have clear := witness.choose_spec.1
      cases current : witness.choose.state with
      | none => rfl
      | some state =>
          rw [current] at clear
          exact clear
  · exact setup.commitRecoveryRetainedInfo_excluded wellFormed who view

/-- Every actual clear auxiliary history is observed at the decoded complete
information of its current view, including its entire signal and own-play word. -/
theorem commitRecoveryClearInformation_observed (wellFormed : setup.WellFormed) (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state) :
    setup.commitRecoveryModel.infoOf who trace =
      setup.commitRecoveryClearInformation wellFormed who
        (setup.commitRecoveryPrivate who state) := by
  classical
  unfold commitRecoveryClearInformation
  split
  · next witness =>
      exact setup.commitRecovery_clear_info_eq who trace witness.choose.trace clear
        witness.choose_spec.1 witness.choose_spec.2.symm
  · next absent => exact (absent ⟨⟨state, trace⟩, clear, rfl⟩).elim

/-- The broader auxiliary decoder agrees with the intended information
injection wherever an initialized intended source history realizes the view. -/
theorem commitRecoveryClearInformation_intended (wellFormed : setup.WellFormed) (who : Player)
    (original : setup.intendedProtocol.History) :
    setup.commitRecoveryClearInformation wellFormed who
        (setup.intendedModel.infoOf who original.trace) =
      setup.commitRecoveryInformation wellFormed who
        (setup.intendedModel.infoOf who original.trace) := by
  have observed := setup.commitRecoveryClearInformation_observed wellFormed who
    (setup.commitRecoveryLiftHistory wellFormed original).trace
    (setup.commitRecoveryLiftHistory_clear wellFormed original)
  rw [setup.commitRecoveryLiftHistory_private] at observed
  exact observed.symm.trans (setup.commitRecoveryInformation_observed wellFormed who original)

end Vegas.SourceProgram.Setup
