/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryAttemptReset
import Vegas.Game.ProposalRecoveryPrescription
import Vegas.Game.ProposalRecoveryContinuation

/-! # One enriched continuation after a shared failed commitment attempt -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- The reset state and every enriched normalized coordinate agree after
same-omission failed attempts. One common prescription therefore supplies the
entire future law; no retry equilibrium is selected independently. -/
theorem proposalRecovery_failed_attempt_terminal_eq
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
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
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.proposalRecoveryPrescribedProfile prescription) ⟨leftState, leftTrace⟩).map
          setup.proposalRecoveryErasedHistory =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.proposalRecoveryPrescribedProfile prescription) ⟨rightState, rightTrace⟩).map
          setup.proposalRecoveryErasedHistory := by
  apply setup.proposalRecovery_terminal_erased_eq
    (setup.proposalRecoveryPrescribedProfile prescription)
    (setup.proposalRecoveryPrescribedProfile_normalized prescription) certificate
  exact setup.proposalRecovery_failed_attempt_erased_eq observer first prior committing
    leftTrace rightTrace leftRetained rightRetained sameOmissions boundary failed

end Vegas.SourceProgram.Setup
