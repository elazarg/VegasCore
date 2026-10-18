/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryLift
import Vegas.Source.CommitRecoveryInstructions

/-! # Lifting complete labeled action words over actual semantic histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoveryJointRecall : ∀ {state : setup.proposalRecoveryProtocol.State},
    setup.proposalRecoveryProtocol.Trace state →
      List (Player → Option (ProposalRecoveryMove Player L))
  | _, .start => []
  | _, .extend prior joint _ _ => joint :: proposalRecoveryJointRecall prior

theorem proposalRecoveryJointRecall_semantic
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryJointRecall trace).map proposalRecoveryJoint =
      setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace trace) := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih => exact congrArg (List.cons _) ih

theorem proposalRecoveryJointRecall_valid
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (member : joint ∈ setup.proposalRecoveryJointRecall trace)
    (who : Player) (move : ProposalRecoveryMove Player L) (selected : joint who = some move) :
    move.Valid := by
  induction trace with
  | start => cases member
  | extend prior current legal supported ih =>
      rcases List.mem_cons.mp member with equal | previous
      · subst joint
        have offered := legal.2 who
        rw [selected] at offered
        exact offered.2.2
      · exact ih previous

theorem proposalRecovery_legal_of_semantic
    {state : setup.proposalRecoveryProtocol.State}
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state (proposalRecoveryJoint joint))
    (valid : ∀ who move, joint who = some move → move.Valid) :
    setup.proposalRecoveryProtocol.Legal state joint := by
  refine ⟨legal.1, ?_⟩
  intro who
  have offered := legal.2 who
  cases selected : joint who with
  | none =>
      change ¬ setup.commitRecoveryProtocol.active state who
      simpa only [proposalRecoveryJoint, selected, Option.map_none] using offered
  | some move =>
      simp only [proposalRecoveryJoint, selected, Option.map_some] at offered
      exact ⟨offered.1, offered.2, valid who move selected⟩

/-- Labels may be chosen from other actual source histories. The result uses
the exact original semantic trace and chance outcomes, not a replacement run. -/
theorem proposalRecovery_lift_joint_word
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (word : List (Player → Option (ProposalRecoveryMove Player L)))
    (semantic : word.map proposalRecoveryJoint = setup.recoveryJointRecall trace)
    (valid : ∀ joint ∈ word, ∀ who move, joint who = some move → move.Valid) :
    ∃ lifted : setup.proposalRecoveryProtocol.Trace state,
      setup.proposalRecoveryEraseTrace lifted = trace ∧
      setup.proposalRecoveryJointRecall lifted = word := by
  induction trace generalizing word with
  | start =>
      have empty : word = [] := List.map_eq_nil_iff.mp semantic
      subst word
      exact ⟨.start, rfl, rfl⟩
  | @extend source target prior current legal supported ih =>
      cases word with
      | nil => cases semantic
      | cons joint rest =>
          have parts := List.cons.inj semantic
          have sameJoint := parts.1
          subst current
          obtain ⟨lifted, erased, recalled⟩ := ih rest parts.2
            (fun next member => valid next (List.mem_cons_of_mem joint member))
          have semanticLegal : setup.commitRecoveryProtocol.Legal source
              (proposalRecoveryJoint joint) := by
            exact legal
          have labeledLegal := setup.proposalRecovery_legal_of_semantic joint semanticLegal
            (valid joint (List.mem_cons_self ..))
          have labeledSupported : target ∈
              (setup.proposalRecoveryProtocol.step source ⟨joint, labeledLegal⟩).support := by
            rw [setup.proposalRecovery_step]
            exact supported
          refine ⟨lifted.extend joint labeledLegal labeledSupported, ?_, ?_⟩
          · change (setup.proposalRecoveryEraseTrace lifted).extend
              (proposalRecoveryJoint joint) _ _ =
                prior.extend (proposalRecoveryJoint joint) legal supported
            rw [erased]
          · exact congrArg (List.cons joint) recalled

end Vegas.SourceProgram.Setup
