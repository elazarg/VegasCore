/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptReset
import Vegas.Game.CommitRecoveryErasedContinuation

/-! # The selected source profile has one failed-attempt continuation law

The common original saved history and omission word determine the entire
erased retry or exhausted history. The original terminal runner gives the
same terminal readout and payoff law for the actual selected source profile.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Actual failed attempts with arbitrary different typed choices have one
terminal readout and payoff law. Reset information equality is derived. -/
theorem commitRecoveryErasedProfile_failed_attempt_terminal_joint_eq
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (sameOmissions :
      (setup.recoveryJointRecall leftTrace).map
          (fun joint owner => CommitRecoveryMove.missed (joint owner)) =
        (setup.recoveryJointRecall rightTrace).map
          (fun joint owner => CommitRecoveryMove.missed (joint owner)))
    (boundary : leftTrace.length + ProtocolState.commitEnd setup.program first.point =
      prior.length + ProtocolState.remaining setup.program first.point)
    (failed : leftState.elim False
      (fun left => (left.excluded \ first.entryExcluded).Nonempty)) :
    (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryErasedProfile profile) ⟨leftState, leftTrace⟩).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryErasedProfile profile) ⟨rightState, rightTrace⟩).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) := by
  apply setup.commitRecoveryErasedProfile_terminal_joint_eq profile utility excludedPayoff
    certificate
  exact setup.commitRecovery_failed_attempt_erased_eq observer first prior committing
    leftTrace rightTrace leftRetained rightRetained sameOmissions boundary failed

end Vegas.SourceProgram.Setup
