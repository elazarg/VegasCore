/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNonmissingSource

/-! # Ordinary source choices at complete clear recovery information -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem clear_lift_menu (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who) (choice : Option (OwnAction Player L))
    (permitted : choice ∈ (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).menu who view) :
    CommitRecoveryMove.lift choice ∈ setup.commitRecoveryModel.menu who
      (setup.commitRecoveryClearInformation wellFormed who view) := by
  cases choice with
  | none =>
      change ¬ setup.commitRecoveryActive who
        (setup.commitRecoveryClearInformation wellFormed who view).1.1
      unfold commitRecoveryActive
      rw [setup.commitRecoveryClearInformation_current]
      cases view with
      | none => exact not_false
      | some view => exact fun active => permitted active.1
  | some action =>
      change setup.commitRecoveryActive who
          (setup.commitRecoveryClearInformation wellFormed who view).1.1 ∧
        (setup.commitRecoveryClearInformation wellFormed who view).1.1.1.elim False
          (fun view => (⟨action, false⟩ : CommitRecoveryMove Player L) ∈
            ProtocolView.recoveryAvailable who setup.program view)
      unfold commitRecoveryActive
      rw [setup.commitRecoveryClearInformation_current,
        setup.commitRecoveryClearInformation_excluded]
      cases view with
      | none => cases permitted
      | some view =>
          simp only [Option.elim_some, Finset.notMem_empty, not_false_eq_true, and_true]
          refine ⟨permitted.1, permitted.2, ?_⟩
          dsimp only
          split
          · intro impossible; cases impossible
          · rfl

/-- Every legal ordinary forfeiture choice has its exact nonmissing recovery
choice at the complete clear information, including an accepted failed binding. -/
def commitRecoveryClearChoice (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who) :
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Choice who view ↪
      setup.commitRecoveryModel.Choice who
        (setup.commitRecoveryClearInformation wellFormed who view) where
  toFun choice := ⟨CommitRecoveryMove.lift choice.1,
    clear_lift_menu setup wellFormed who view choice.1 choice.2⟩
  inj' _ _ same := Subtype.ext
    (CommitRecoveryMove.lift_injective (congrArg Subtype.val same))

/-- Forgetting the omission flag retracts the exact ordinary source choice. -/
theorem commitRecoveryUnderlyingChoice_clear (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who)
    (choice : (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Choice
      who view) :
    setup.commitRecoveryUnderlyingChoice wellFormed who view
        (setup.commitRecoveryClearChoice wellFormed who view choice) = choice :=
  Subtype.ext (CommitRecoveryMove.underlying_lift choice.1)

/-- A recovery choice with no omission is exactly the lift of its ordinary
underlying action; its typed result and source action name are unchanged. -/
theorem commitRecoveryClearChoice_underlying (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who)
    (choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryClearInformation wellFormed who view))
    (nonmissing : CommitRecoveryMove.missed choice.1 = false) :
    setup.commitRecoveryClearChoice wellFormed who view
        (setup.commitRecoveryUnderlyingChoice wellFormed who view choice) = choice := by
  apply Subtype.ext
  change CommitRecoveryMove.lift (CommitRecoveryMove.underlying choice.1) = choice.1
  cases selected : choice.1 with
  | none => rfl
  | some move =>
      cases move with
      | mk action missing =>
          have flag : missing = false := by simpa only [selected, CommitRecoveryMove.missed,
            Option.elim_some] using nonmissing
          subst missing
          rfl

/-- At every genuine clear running source history, lifting the original
ordinary nonmissing policy recovers the SAME conditional auxiliary choice law.
No accepted failure or future opening choice is discarded. -/
theorem commitRecoveryNonmissingSourcePolicy_clear_law
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    ((setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who)
      (setup.commitRecoveryPrivate who history.state)).map
        (setup.commitRecoveryClearChoice wellFormed who
          (setup.commitRecoveryPrivate who history.state)) =
      setup.commitRecoveryNonmissingProfile assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who
          (setup.commitRecoveryPrivate who history.state)) := by
  unfold commitRecoveryNonmissingSourcePolicy
  rw [PMF.map_comp]
  calc
    _ = (setup.commitRecoveryNonmissingProfile assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who
          (setup.commitRecoveryPrivate who history.state))).map id := by
      apply map_congr_on_support
      intro choice supported
      apply setup.commitRecoveryClearChoice_underlying
      have observed := setup.commitRecoveryClearInformation_observed wellFormed who
        history.trace clear
      have present := setup.commitRecovery_nonmissing_present assessment mixed history running who
      rw [observed] at present
      exact (mem_support_fiberPosterior present supported).1
    _ = _ := PMF.map_id _

end Vegas.SourceProgram.Setup
