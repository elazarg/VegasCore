/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryPublicSuccessor
import Vegas.Source.CommitRecoveryPrivateWordSwap
import Vegas.Source.CommitRecoveryAttemptReset
import Vegas.Source.CommitRecoveryNonCommitObservation

/-! # Full source observations from public words and private instructions

The real source dispatcher retains the observer's saved view. Its clean,
retry and exhausted branches are derived from supported original steps.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A supported original instruction transports an observer's complete live
and saved source views when its raw coordinate and public successor agree.
The observer may already be excluded. -/
theorem commitRecovery_step_observed_eq (who : Player)
    (first second : CommitRecoveryState setup.program)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some first))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some second))
    (point : ProtocolState.observe who setup.program first.point =
      ProtocolState.observe who setup.program second.point)
    (saved : ProtocolState.observe who setup.program first.saved =
      ProtocolState.observe who setup.program second.saved)
    (excluded : first.excluded = second.excluded)
    (entryExcluded : first.entryExcluded = second.entryExcluded)
    (generation : first.generation = second.generation)
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (ownChoice : leftJoint who = rightJoint who)
    (leftNext rightNext : CommitRecoveryState setup.program)
    (leftSupport : leftNext ∈ (first.step leftJoint).support)
    (rightSupport : rightNext ∈ (second.step rightJoint).support)
    (publicNext : setup.attemptPublicSignal who (some leftNext) =
      setup.attemptPublicSignal who (some rightNext)) :
    (ProtocolState.observe who setup.program leftNext.point,
      ProtocolState.observe who setup.program leftNext.saved,
      leftNext.excluded, leftNext.entryExcluded, leftNext.generation) =
    (ProtocolState.observe who setup.program rightNext.point,
      ProtocolState.observe who setup.program rightNext.saved,
      rightNext.excluded, rightNext.entryExcluded, rightNext.generation) := by
  have exclusions : leftNext.excluded = rightNext.excluded :=
    congrArg (fun signal => signal.2.1) publicNext
  by_cases committing : ProtocolState.atCommit setup.program first.point = true
  · obtain ⟨left, leftRaw, rfl⟩ := first.step_raw_result leftJoint leftNext leftSupport
    obtain ⟨right, rightRaw, rfl⟩ := second.step_raw_result rightJoint rightNext rightSupport
    have rawExclusions : left.1.2 = right.1.2 := by
      simpa only [CommitRecoveryState.close_excluded, CommitRecoveryState.install] using exclusions
    have rawPoint := ProtocolState.recoveryStep_commit_observe_congr who setup.program
      first.point second.point point committing first.excluded leftJoint rightJoint ownChoice
      left.1 leftRaw right.1 (by simpa only [excluded] using rightRaw)
    exact CommitRecoveryState.close_observed_congr who
      (first.install left.1 left.2) (second.install right.1 right.2)
      rawPoint saved rawExclusions entryExcluded generation
  · have notCommit : ProtocolState.atCommit setup.program first.point = false := by
      exact Bool.eq_false_iff.mpr committing
    have secondNotCommit : ProtocolState.atCommit setup.program second.point = false := by
      rw [← ProtocolState.atCommit_observe setup.program second.point who, ← point,
        ProtocolState.atCommit_observe, notCommit]
    obtain ⟨left, leftRaw, rfl⟩ := first.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier firstTrace) notCommit leftJoint leftNext leftSupport
    obtain ⟨right, rightRaw, rfl⟩ := second.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier secondTrace) secondNotCommit rightJoint rightNext
        rightSupport
    have publicView : ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program left.1) =
      ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program right.1) :=
      Option.some.inj (congrArg Prod.fst publicNext)
    have rawPoint := ProtocolState.recoveryStep_noncommit_observe_congr who setup.program
      first.point second.point point notCommit first.excluded leftJoint rightJoint ownChoice
      left leftRaw right (by simpa only [excluded] using rightRaw) publicView
    simp only [CommitRecoveryState.atPoint] at exclusions ⊢
    rw [rawPoint, exclusions, generation]

end Vegas.SourceProgram.Setup
