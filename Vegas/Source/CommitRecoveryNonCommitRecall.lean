/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNonCommitObservation
import Vegas.Source.CommitRecoveryPredecessor

/-! # Actual surviving observations before noncommitment recovery steps -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Setup

/-- Genuine noncommitment steps preserve enough observed information to
recover the previous private signal, with arbitrary permanent exclusions. -/
theorem commitRecovery_noncommit_predecessor_private
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (first second : CommitRecoveryState setup.program)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some first))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some second))
    (firstJoint secondJoint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal (some first) firstJoint)
    (secondLegal : setup.commitRecoveryProtocol.Legal (some second) secondJoint)
    (firstAfter secondAfter : setup.commitRecoveryProtocol.State)
    (firstReached : firstAfter ∈
      (setup.commitRecoveryProtocol.step (some first) ⟨firstJoint, firstLegal⟩).support)
    (secondReached : secondAfter ∈
      (setup.commitRecoveryProtocol.step (some second) ⟨secondJoint, secondLegal⟩).support)
    (firstNotCommit : ProtocolState.atCommit setup.program first.point = false)
    (secondNotCommit : ProtocolState.atCommit setup.program second.point = false)
    (firstSurvives : who ∉ first.excluded) (secondSurvives : who ∉ second.excluded)
    (after : setup.commitRecoveryPrivate who firstAfter =
      setup.commitRecoveryPrivate who secondAfter) :
    setup.commitRecoveryPrivate who (some first) =
      setup.commitRecoveryPrivate who (some second) := by
  obtain ⟨left, leftReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstReached
  obtain ⟨right, rightReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondReached
  obtain ⟨leftRaw, leftRawReached, rfl⟩ := first.step_noncommit_atPoint
    (setup.commitRecovery_blockFrontier firstTrace) firstNotCommit firstJoint left leftReached
  obtain ⟨rightRaw, rightRawReached, rfl⟩ := second.step_noncommit_atPoint
    (setup.commitRecovery_blockFrontier secondTrace) secondNotCommit secondJoint right rightReached
  change some (ProtocolState.observe who setup.program leftRaw.1) =
    some (ProtocolState.observe who setup.program rightRaw.1) at after
  exact congrArg some (ProtocolView.recoveryStep_predecessor_eq who setup.program first.point
    second.point first.excluded second.excluded firstJoint secondJoint leftRaw rightRaw
    firstLegal.1 secondLegal.1 leftRawReached rightRawReached firstSurvives secondSurvives
    (Option.some.inj after))

end Setup
end Vegas.SourceProgram
