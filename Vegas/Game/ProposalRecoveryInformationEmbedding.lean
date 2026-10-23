/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoverySuccessfulTrace
import Vegas.Game.ProposalRecoveryInformationReadback
import Vegas.Game.ProposalRecoveryArchivePublicHistory
import Vegas.Game.CommitRecoveryInformationEmbedding

/-! # Full intended-source information retained by the labeled refinement -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem ordinary_coordinate (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryJointRecall
        (setup.proposalRecoveryLiftTrace (fun _ _ => false) trace)).map (fun joint => joint who) =
      ((setup.recoveryJointRecall trace).map (fun joint => joint who)).map
        (Option.map ProposalRecoveryMove.ordinary) := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      simp only [proposalRecoveryLiftTrace, proposalRecoveryJointRecall,
        recoveryJointRecall, List.map_cons, ih]
      congr 1
      change (joint who).map (fun move => ProposalRecoveryMove.label move false) =
        (joint who).map ProposalRecoveryMove.ordinary
      cases joint who with
      | none => rfl
      | some move =>
          rcases move with ⟨action, missing⟩
          cases action with
          | commit => rfl
          | reveal _ _ bit => cases bit <;> rfl

/-- Ordinary clear lifts retain no extra information beyond the actual OLD
full source information. The proposal archive is derived from successful
public result cells; it is not supplied as a fiber-equality premise. -/
theorem proposalRecovery_clear_ordinary_information_eq (who : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftState)
    (right : setup.commitRecoveryProtocol.Trace rightState)
    (leftClear : setup.CommitRecoveryClear leftState)
    (rightClear : setup.CommitRecoveryClear rightState)
    (same : setup.commitRecoveryModel.infoOf who left =
      setup.commitRecoveryModel.infoOf who right) :
    setup.proposalRecoveryModel.infoOf who
        (setup.proposalRecoveryLiftTrace (fun _ _ => false) left) =
      setup.proposalRecoveryModel.infoOf who
        (setup.proposalRecoveryLiftTrace (fun _ _ => false) right) := by
  have privateSame : setup.commitRecoveryPrivate who leftState =
      setup.commitRecoveryPrivate who rightState := by
    have current := congrArg (fun information => information.1.1) same
    have leftRead : (setup.commitRecoveryModel.infoOf who left).1.1 =
        (setup.commitRecoveryPrivate who leftState, setup.commitRecoveryPublic leftState) := by
      cases left <;> rfl
    have rightRead : (setup.commitRecoveryModel.infoOf who right).1.1 =
        (setup.commitRecoveryPrivate who rightState, setup.commitRecoveryPublic rightState) := by
      cases right <;> rfl
    rw [leftRead, rightRead] at current
    exact congrArg Prod.fst current
  apply setup.proposalRecovery_info_eq_of_semantic_public_coordinate
  · simpa only [setup.proposalRecoveryEraseTrace_lift] using same
  · apply setup.proposalRecoveryPublicRecall_eq_of_erased_archive
    · simpa only [setup.proposalRecoveryEraseTrace_lift] using
        congrArg (setup.commitRecoveryErasedInformation who) same
    · rw [setup.proposalRecovery_clear_ordinary_archive who left leftClear,
        setup.proposalRecovery_clear_ordinary_archive who right rightClear, privateSame]
  · rw [setup.ordinary_coordinate, setup.ordinary_coordinate,
      setup.commitRecovery_coordinate_eq_of_info_eq who left right same]

/-- The existing actual intended recovery trace, with ordinary proposal
labels. Both operational states and all chance outcomes are inherited. -/
def proposalRecoveryIntendedLift (wellFormed : setup.WellFormed)
    (original : setup.intendedProtocol.History) : setup.proposalRecoveryProtocol.History :=
  let old := setup.commitRecoveryLiftHistory wellFormed original
  ⟨old.state, setup.proposalRecoveryLiftTrace (fun _ _ => false) old.trace⟩

private theorem current_private (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryModel.infoOf who trace).1.1.1 =
      setup.commitRecoveryPrivate who state := by
  cases trace <;> rfl

/-- A full retained-information readout, defined on all original source
views. Unreachable views retain their literal current private component. -/
def proposalRecoveryRetainedInformation (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who) : setup.proposalRecoveryModel.InfoState who := by
  classical
  exact if witness : ∃ original : setup.intendedProtocol.History,
      setup.intendedModel.infoOf who original.trace = view then
    setup.proposalRecoveryModel.infoOf who
      (setup.proposalRecoveryIntendedLift wellFormed witness.choose).trace
  else (((view, ((∅, 0, 0), none)), []), [])

theorem proposalRecoveryRetainedInformation_current (wellFormed : setup.WellFormed)
    (who : Player) (view : setup.intendedModel.InfoState who) :
    (setup.proposalRecoveryRetainedInformation wellFormed who view).1.1.1 = view := by
  classical
  unfold proposalRecoveryRetainedInformation
  split
  · next witness =>
      rw [setup.current_private]
      exact (setup.commitRecoveryLiftHistory_private wellFormed who witness.choose).trans
        witness.choose_spec
  · rfl

/-- Injective intended full-information embedding into the actual labeled
recovery information model, not just its forgetful semantic projection. -/
def proposalRecoveryInformation (wellFormed : setup.WellFormed) (who : Player) :
    setup.intendedModel.InfoState who ↪ setup.proposalRecoveryModel.InfoState who where
  toFun := setup.proposalRecoveryRetainedInformation wellFormed who
  inj' := by
    intro first second same
    simpa only [setup.proposalRecoveryRetainedInformation_current] using
      congrArg (fun information => information.1.1.1) same

theorem proposalRecoveryInformation_observed (wellFormed : setup.WellFormed) (who : Player)
    (original : setup.intendedProtocol.History) :
    setup.proposalRecoveryModel.infoOf who
        (setup.proposalRecoveryIntendedLift wellFormed original).trace =
      setup.proposalRecoveryInformation wellFormed who
        (setup.intendedModel.infoOf who original.trace) := by
  classical
  change _ = setup.proposalRecoveryRetainedInformation wellFormed who _
  unfold proposalRecoveryRetainedInformation
  split
  · next witness =>
      apply setup.proposalRecovery_clear_ordinary_information_eq
      · exact setup.commitRecoveryLiftHistory_clear wellFormed original
      · exact setup.commitRecoveryLiftHistory_clear wellFormed witness.choose
      · rw [setup.commitRecoveryInformation_observed,
          setup.commitRecoveryInformation_observed, witness.choose_spec]
  · next absent => exact (absent ⟨original, rfl⟩).elim

end Vegas.SourceProgram.Setup
