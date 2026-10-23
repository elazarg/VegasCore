/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryWordLift

/-! # Exact labeled source histories from their semantic trace and joint word -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryTrace_eq_of_semantic_word
    {state : setup.proposalRecoveryProtocol.State}
    (left right : setup.proposalRecoveryProtocol.Trace state)
    (semantic : setup.proposalRecoveryEraseTrace left = setup.proposalRecoveryEraseTrace right)
    (word : setup.proposalRecoveryJointRecall left = setup.proposalRecoveryJointRecall right) :
    left = right := by
  induction left with
  | start =>
      cases right with
      | start => rfl
      | extend prior joint legal supported => cases word
  | extend prior joint legal supported ih =>
      cases right with
      | start => cases word
      | extend other otherJoint otherLegal otherSupport =>
          have parts := List.cons.inj word
          simp only [proposalRecoveryEraseTrace, Trace.extend.injEq] at semantic
          rcases semantic with ⟨rfl, priorEq, _jointEq⟩
          have earlier := ih other (eq_of_heq priorEq) parts.2
          cases earlier
          cases parts.1
          rfl

theorem proposalRecoveryHistory_eq_of_semantic_word
    (left right : setup.proposalRecoveryProtocol.History)
    (semantic : (⟨left.state, setup.proposalRecoveryEraseTrace left.trace⟩ :
        setup.commitRecoveryProtocol.History) =
      ⟨right.state, setup.proposalRecoveryEraseTrace right.trace⟩)
    (word : setup.proposalRecoveryJointRecall left.trace =
      setup.proposalRecoveryJointRecall right.trace) : left = right := by
  rcases left with ⟨leftState, leftTrace⟩
  rcases right with ⟨rightState, rightTrace⟩
  have stateEq := congrArg History.state semantic
  change leftState = rightState at stateEq
  subst rightState
  have traces : setup.proposalRecoveryEraseTrace leftTrace =
      setup.proposalRecoveryEraseTrace rightTrace := by
    simpa only [History.mk.injEq, heq_eq_eq, true_and] using semantic
  have same := setup.proposalRecoveryTrace_eq_of_semantic_word leftTrace rightTrace traces word
  cases same
  rfl

end Vegas.SourceProgram.Setup
