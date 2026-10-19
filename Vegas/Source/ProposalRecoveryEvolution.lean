/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoverySupportSplice

/-! # Actual one-step evolution of erased source controls and proposal words -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

abbrev ProposalRecoveryHistoryImage :=
  (setup.commitRecoveryProtocol.State ×
    ((who : Player) → setup.commitRecoveryModel.InfoState who)) ×
      List (Option (ProposalRecoveryProposal L))

def proposalRecoveryNextErasedHistory (before : setup.ProposalRecoveryHistoryImage)
    (next : setup.commitRecoveryProtocol.State × Option (ProposalRecoveryProposal L)) :
    setup.ProposalRecoveryHistoryImage :=
  (setup.commitRecoveryNextErasedHistory before.1 next.1, next.2 :: before.2)

theorem proposalRecoveryErasedHistory_extend
    (history : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal history.state joint)
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈
      (setup.proposalRecoveryProtocol.step history.state ⟨joint, legal⟩).support) :
    setup.proposalRecoveryErasedHistory (history.extend legal supported) =
      setup.proposalRecoveryNextErasedHistory (setup.proposalRecoveryErasedHistory history)
        (target.map CommitRecoveryState.eraseHistory,
          setup.proposalRecoveryProposalOf history.state joint) := by
  apply Prod.ext
  · exact setup.commitRecoveryErasedHistory_extend
      ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩
      (proposalRecoveryJoint joint) (setup.proposalRecovery_erase_legal joint legal) supported
  · rfl

variable [Fintype Player]

/-- The actual one-step law retains the erased semantic state, every player's
erased information and the complete proposal-delta word. -/
theorem proposalRecovery_oneStep_image
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (history : setup.proposalRecoveryProtocol.History)
    (running : ¬ setup.proposalRecoveryProtocol.terminal history.state) :
    (setup.proposalRecoveryModel.runBehavioralFrom profile 1 history).map
        setup.proposalRecoveryErasedHistory =
      (setup.proposalRecoveryModel.behavioralJoint profile history.trace running).bind fun draw =>
        (setup.proposalRecoveryProtocol.step history.state draw).map fun target =>
          setup.proposalRecoveryNextErasedHistory (setup.proposalRecoveryErasedHistory history)
            (target.map CommitRecoveryState.eraseHistory,
              setup.proposalRecoveryProposalOf history.state draw.1) := by
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ 0 running, PMF.map_bind]
  apply congrArg (PMF.bind _)
  funext draw
  change ((setup.proposalRecoveryProtocol.step history.state draw).bindOnSupport
    (fun target realized => PMF.pure (history.extend draw.2 realized))).map
      setup.proposalRecoveryErasedHistory = _
  simp only [map_bindOnSupport, PMF.pure_map]
  rw [← pmf_bind_pure_eq_map]
  apply bindOnSupport_eq_bind_of_eq_on_support
  intro target realized
  exact congrArg PMF.pure
    (setup.proposalRecoveryErasedHistory_extend history draw.1 draw.2 realized)

/-- Dependence on the actual normalized query is a prescription property;
the complete one-step image law is derived from the original source kernel. -/
theorem proposalRecovery_oneStep_erased_eq
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (normalized : ∀ who first second,
      setup.proposalRecoveryQuery who first = setup.proposalRecoveryQuery who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second)
    (running : ¬ setup.proposalRecoveryProtocol.terminal first.state) :
    (setup.proposalRecoveryModel.runBehavioralFrom profile 1 first).map
        setup.proposalRecoveryErasedHistory =
      (setup.proposalRecoveryModel.runBehavioralFrom profile 1 second).map
        setup.proposalRecoveryErasedHistory := by
  have stateEq := congrArg Prod.fst (congrArg Prod.fst same)
  have secondRunning : ¬ setup.proposalRecoveryProtocol.terminal second.state :=
    fun stopped => running ((setup.commitRecovery_terminal_eq_of_erased stateEq).mpr stopped)
  have jointEq :
      (setup.proposalRecoveryModel.behavioralJoint profile first.trace running).map Subtype.val =
        (setup.proposalRecoveryModel.behavioralJoint profile second.trace secondRunning).map
          Subtype.val := by
    rw [InformationModel.behavioralJoint_map_val, InformationModel.behavioralJoint_map_val]
    congr 1
    funext who
    exact normalized who _ _
      (setup.proposalRecoveryQuery_eq_of_erased_history first second same who)
  rw [setup.proposalRecovery_oneStep_image profile first running,
    setup.proposalRecovery_oneStep_image profile second secondRunning]
  apply bind_eq_of_map_eq _ _ Subtype.val Subtype.val jointEq
  intro left _leftSupport right _rightSupport joints
  rcases left with ⟨left, leftLegal⟩
  rcases right with ⟨right, rightLegal⟩
  dsimp only at joints
  subst right
  have raw := setup.proposalRecovery_step_erased_eq stateEq left leftLegal rightLegal
  have mapped := congrArg
    (PMF.map
      (setup.proposalRecoveryNextErasedHistory (setup.proposalRecoveryErasedHistory first))) raw
  rw [← same]
  convert mapped using 1 <;> rw [PMF.map_comp] <;> rfl

end Vegas.SourceProgram.Setup
