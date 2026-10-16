/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNoMissRepresentative
import Vegas.Game.CommitRecoveryAttemptReset

/-! # Original source continuation under the selected reduced-query prescription

The legal source profile reads its value law at the genuine no-new-omission
query with remembered private words erased. Its failed-attempt continuation
uses the original terminal runner, retaining all future failure and rescue
branches.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Read a source prescription at the genuine no-new-omission query, while
transporting the same underlying action back to the original legal menu. -/
def commitRecoveryNoMissProfile
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ who, setup.commitRecoveryModel.BehavioralPolicy who := fun who info =>
  (profile who (setup.commitRecoveryNoMissInformation who info)).map
    (setup.commitRecoveryNoMissChoice who info).symm

theorem commitRecoveryNoMissProfile_raw
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissProfile profile who info).map Subtype.val =
      (profile who (setup.commitRecoveryNoMissInformation who info)).map Subtype.val := by
  rw [commitRecoveryNoMissProfile, PMF.map_comp]
  rfl

/-- This profile belongs to the original full-information source game. Its
query is the combined reduced label; its runner and observations are unchanged. -/
def commitRecoveryNoMissErasedProfile
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ who, setup.commitRecoveryModel.BehavioralPolicy who :=
  setup.commitRecoveryErasedProfile (setup.commitRecoveryNoMissProfile profile)

/-- The actual selected policy reads exactly the combined source query,
without assuming a raw-law equality or changing the legal action. -/
theorem commitRecoveryNoMissErasedProfile_raw
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissErasedProfile profile who info).map Subtype.val =
      (profile who (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who info))).map Subtype.val := by
  rw [commitRecoveryNoMissErasedProfile, setup.commitRecoveryErasedProfile_raw,
    setup.commitRecoveryNoMissProfile_raw, ← setup.commitRecoveryNoMissInformation_erased]

/-- Applying the current-attempt normalization does not change the selected
source action law. This is a property of the constructed profile. -/
theorem commitRecoveryNoMissErasedProfile_normalized
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissErasedProfile profile who
        (setup.commitRecoveryNoMissInformation who info)).map Subtype.val =
      (setup.commitRecoveryNoMissErasedProfile profile who info).map Subtype.val := by
  rw [setup.commitRecoveryNoMissErasedProfile_raw, setup.commitRecoveryNoMissErasedProfile_raw,
    setup.commitRecoveryNoMissInformation_idempotent]

variable [Fintype Player]

/-- Two actual failed attempts from the same saved history and omission word
have one full terminal readout/payoff law under this actual prescription.
Future accepted-failure rescue and exhausted restore are retained. -/
theorem commitRecoveryNoMissErasedProfile_failed_attempt_terminal_joint_eq
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
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
        (setup.commitRecoveryNoMissErasedProfile profile) ⟨leftState, leftTrace⟩).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryNoMissErasedProfile profile) ⟨rightState, rightTrace⟩).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) :=
  setup.commitRecoveryErasedProfile_failed_attempt_terminal_joint_eq
    (setup.commitRecoveryNoMissProfile profile) utility excludedPayoff certificate
    observer first prior committing leftTrace rightTrace leftRetained rightRetained
    sameOmissions boundary failed

end Vegas.SourceProgram.Setup
