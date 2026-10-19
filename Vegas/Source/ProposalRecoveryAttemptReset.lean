/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryCommitWindow
import Vegas.Source.CommitRecoveryAttemptReset

/-! # Full enriched reset images from the original shared commitment attempt -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The existing actual reset comparison keeps the full proposal chronology:
commitment steps add only silent deltas, so no canceled value becomes evidence. -/
theorem proposalRecovery_failed_attempt_erased_eq
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (leftTrace : setup.proposalRecoveryProtocol.Trace leftState)
    (rightTrace : setup.proposalRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (sameOmissions :
      (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace leftTrace)).map
          (fun joint owner => CommitRecoveryMove.missed (joint owner)) =
        (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace rightTrace)).map
          (fun joint owner => CommitRecoveryMove.missed (joint owner)))
    (boundary : leftTrace.length + ProtocolState.commitEnd setup.program first.point =
      prior.length + ProtocolState.remaining setup.program first.point)
    (failed : leftState.elim False
      (fun left => (left.excluded \ first.entryExcluded).Nonempty)) :
    setup.proposalRecoveryErasedHistory ⟨leftState, leftTrace⟩ =
      setup.proposalRecoveryErasedHistory ⟨rightState, rightTrace⟩ := by
  have lengths := congrArg List.length sameOmissions
  simp only [List.length_map, setup.recoveryJointRecall_length,
    setup.proposalRecoveryEraseTrace_length] at lengths
  apply Prod.ext
  · exact setup.commitRecovery_failed_attempt_erased_eq observer first
      (setup.proposalRecoveryEraseTrace prior) committing
      (setup.proposalRecoveryEraseTrace leftTrace) (setup.proposalRecoveryEraseTrace rightTrace)
      (setup.proposalRecoveryEraseTrace_prefix leftRetained)
      (setup.proposalRecoveryEraseTrace_prefix rightRetained) sameOmissions
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using boundary) failed
  · change setup.proposalRecoveryDeltaRecall leftTrace =
      setup.proposalRecoveryDeltaRecall rightTrace
    rw [setup.proposalRecoveryDeltaRecall_commit_window first prior committing leftTrace
        leftRetained boundary.le,
      setup.proposalRecoveryDeltaRecall_commit_window first prior committing rightTrace
        rightRetained (by omega), lengths]

end Vegas.SourceProgram.Setup
