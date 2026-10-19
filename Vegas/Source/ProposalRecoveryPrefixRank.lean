/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNonCommitObservation
import Vegas.Source.CommitRecoverySavedProgress
import Vegas.Source.ProposalRecoveryAddress

/-! # Consumed publication steps precede surviving source cursors -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A consumed noncommit step is strictly before every later surviving
source cursor, even across commitment resets. Its static publication-block
address is therefore also strictly before that cursor. -/
theorem proposalRecovery_noncommit_prefix_rank_lt
    (who : Player) (before current : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some before))
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some before) joint)
    {target : setup.commitRecoveryProtocol.State}
    (supported : target ∈
      (setup.commitRecoveryProtocol.step (some before) ⟨joint, legal⟩).support)
    (kept : TracePrefix (prior.extend joint legal supported) trace)
    (notCommit : ProtocolState.atCommit setup.program before.point = false)
    (survives : who ∉ current.excluded) :
    instructionCount setup.program - ProtocolState.remaining setup.program before.point <
        instructionCount setup.program - ProtocolState.remaining setup.program current.point ∧
      setup.program.publicationBlockLow
          (instructionCount setup.program - ProtocolState.remaining setup.program before.point) <
        instructionCount setup.program - ProtocolState.remaining setup.program current.point := by
  obtain ⟨after, afterSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨raw, rawSupport, installed⟩ := before.step_noncommit_atPoint
    (setup.commitRecovery_blockFrontier prior) notCommit joint after afterSupport
  have consumed := ProtocolState.recoveryStep_remaining setup.program before.point
    before.excluded joint raw legal.1 rawSupport
  have savedStep : ProtocolState.remaining setup.program after.saved + 1 =
      ProtocolState.remaining setup.program before.point := by
    rw [installed]
    exact consumed
  have monotone := setup.commitRecovery_saved_remaining_le_of_prefix who
    (prior.extend joint legal supported) trace kept survives
  change ProtocolState.remaining setup.program current.saved ≤
    ProtocolState.remaining setup.program after.saved at monotone
  have readback := setup.commitRecovery_saved_rank who trace survives
  have position := ProtocolView.atRank_le_position who setup.program _ _ _ readback
  have currentRank := ProtocolView.position_add_remaining who setup.program current.point
  have currentBound := ProtocolState.remaining_le_instructionCount setup.program current.point
  have savedBound := ProtocolState.remaining_le_instructionCount setup.program current.saved
  have beforeBound := ProtocolState.remaining_le_instructionCount setup.program before.point
  have rank : instructionCount setup.program - ProtocolState.remaining setup.program before.point <
      instructionCount setup.program - ProtocolState.remaining setup.program current.point := by
    omega
  exact ⟨rank, (setup.program.publicationBlockLow_le _).trans_lt rank⟩

end Vegas.SourceProgram.Setup
