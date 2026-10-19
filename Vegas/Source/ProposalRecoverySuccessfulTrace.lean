/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoverySuccessfulStep
import Vegas.Source.ProposalRecoveryLift
import Vegas.Source.CommitRecoveryProjection

/-! # Exact proposal words of genuinely clear ordinary recovery histories -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

theorem successfulProposalWord_step {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (before : CommitRecoveryState program)
    (clear : before.excluded = ∅) (joint : Player → Option (CommitRecoveryMove Player L))
    (after : CommitRecoveryState program) (supported : after ∈ (before.step joint).support)
    (afterClear : after.excluded = ∅) (who : Player) :
    ProtocolView.successfulProposalWord who program
        (ProtocolState.observe who program after.point) =
      ProtocolView.successfulProposalWord who program
          (ProtocolState.observe who program before.point) ++
        (ProtocolState.recoveryProposal program before.point
          (fun owner => (joint owner).map ProposalRecoveryMove.ordinary)).toList := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have rawMember : result.1 ∈
      (ProtocolState.recoveryStep program before.point before.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program before.point before.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program before.point
        before.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have resultClear : result.1.2 = ∅ := by
    simpa only [close_excluded, install] using afterClear
  have noFailure : ¬ (before.install result.1 result.2).NewFailure := by
    simp only [NewFailure, install, resultClear, Finset.empty_sdiff,
      Finset.not_nonempty_empty, not_false_eq_true]
  rw [close_point_of_no_new_failure _ noFailure]
  exact ProtocolView.successfulProposalWord_recoveryStep who program before.point joint result.1
    (by simpa only [clear] using rawMember) resultClear

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem label_false (move : CommitRecoveryMove Player L) :
    ProposalRecoveryMove.label move false = ProposalRecoveryMove.ordinary move := by
  rcases move with ⟨action, missing⟩
  cases action with
  | commit => rfl
  | reveal _ _ bit => cases bit <;> rfl

private theorem ordinary_lift_joint (event : setup.commitRecoveryProtocol.StepEvent) :
    setup.proposalRecoveryLiftJoint (fun _ _ => false) event =
      fun owner => (event.joint owner).map ProposalRecoveryMove.ordinary := by
  funext owner
  cases selected : event.joint owner <;>
    simp only [proposalRecoveryLiftJoint, selected, Option.map_none, Option.map_some, label_false]

/-- Clear histories never retry. Each ordinary proposal is therefore the
generation-zero successful publication read from the SAME original view. -/
theorem proposalRecovery_clear_ordinary_word (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state) (_clear : setup.CommitRecoveryClear state),
      setup.proposalRecoveryProposalWord who
          (setup.proposalRecoveryModel.infoOf who
            (setup.proposalRecoveryLiftTrace (fun _ _ => false) trace)) =
        ((setup.commitRecoveryPrivate who state).toList.flatMap fun view =>
          (ProtocolView.successfulProposalWord who setup.program view).map fun pair =>
            (⟨⟨setup.program.publicationBlockLow pair.1, 0, pair.1⟩,
              pair.2.1, pair.2.2⟩ : ProposalRecoveryProposal L))
  | _, .start, _clear => rfl
  | after, @Trace.extend _ _ before _ prior joint legal supported, clear => by
      have beforeClear := setup.commitRecoveryClear_before ⟨joint, legal⟩ supported clear
      have previous := proposalRecovery_clear_ordinary_word who prior beforeClear
      rw [proposalRecoveryLiftTrace, setup.proposalRecoveryProposalWord_extend, previous]
      rw [setup.ordinary_lift_joint]
      cases before with
      | none =>
          obtain ⟨input, _drawn, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          cases equal
          simp only [proposalRecoveryProposalOf_initial, Option.toList_none, List.append_nil,
            commitRecoveryPrivate, Option.map_none, Option.toList_none, List.flatMap_nil,
            Option.map_some, Option.toList_some, List.flatMap_cons,
            CommitRecoveryState.atPoint,
            ProtocolView.successfulProposalWord_entry, List.map_nil]
      | some current =>
          obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have currentClear : current.excluded = ∅ := beforeClear
          have generation := setup.commitRecovery_generation_bound prior current rfl
          have entered : current.entryExcluded = ∅ :=
            Finset.subset_empty.mp (beforeClear ▸ current.entered)
          have zero : current.generation = 0 := by
            rw [entered, Finset.card_empty] at generation
            omega
          have word := current.successfulProposalWord_step beforeClear joint next reached clear who
          simp only [commitRecoveryPrivate, Option.map_some, Option.toList_some,
            List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [word, List.map_append]
          simp only [proposalRecoveryProposalOf, Option.bind_some, currentClear,
            Finset.notMem_empty, ite_false, zero, Option.toList_map]

/-- The canonical archive of an ordinary clear lift is an actual function
of the original source observation, including every successful typed value. -/
theorem proposalRecovery_clear_ordinary_archive (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state) :
    setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who
          (setup.proposalRecoveryLiftTrace (fun _ _ => false) trace)) =
      setup.proposalRecoverySuccessfulArchive who (setup.commitRecoveryPrivate who state) := by
  unfold proposalRecoveryArchive proposalRecoverySuccessfulArchive
  rw [setup.proposalRecovery_clear_ordinary_word who trace clear]

end Setup
end Vegas.SourceProgram
