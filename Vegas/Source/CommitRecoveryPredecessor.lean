/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryRanks

/-! # Exact earlier observations of surviving source recovery instructions -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolView

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The predecessor observation of an actual recovery instruction is recovered
at its original source rank, without deleting foreign automatic actions. -/
theorem recover_recoveryStep {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player)
    (reached : result ∈ (ProtocolState.recoveryStep program point excluded joint).support)
    (survives : who ∉ excluded) :
    atRank who program (position who program (ProtocolState.observe who program point))
        (ProtocolState.observe who program result.1) =
      some (ProtocolState.observe who program point) := by
  rw [atRank_recoveryStep who program point excluded joint result reached survives _ le_rfl]
  exact atRank_position who program _

/-- Equal reached raw observations have equal genuine predecessors for a
surviving owner. The source instruction rank follows from actual step progress,
including missing and automatic foreign commitments and disclosures. -/
theorem recoveryStep_predecessor_eq {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O)
    (first second : ProtocolState program) (firstExcluded secondExcluded : Finset Player)
    (firstJoint secondJoint : Player → Option (CommitRecoveryMove Player L))
    (firstResult secondResult : ProtocolState program × Finset Player)
    (firstRunning : ¬ ProtocolState.terminal program first)
    (secondRunning : ¬ ProtocolState.terminal program second)
    (firstReached : firstResult ∈
      (ProtocolState.recoveryStep program first firstExcluded firstJoint).support)
    (secondReached : secondResult ∈
      (ProtocolState.recoveryStep program second secondExcluded secondJoint).support)
    (firstSurvives : who ∉ firstExcluded) (secondSurvives : who ∉ secondExcluded)
    (observed : ProtocolState.observe who program firstResult.1 =
      ProtocolState.observe who program secondResult.1) :
    ProtocolState.observe who program first = ProtocolState.observe who program second := by
  have firstProgress := ProtocolState.recoveryStep_remaining program first firstExcluded
    firstJoint firstResult firstRunning firstReached
  have secondProgress := ProtocolState.recoveryStep_remaining program second secondExcluded
    secondJoint secondResult secondRunning secondReached
  have firstBefore := position_add_remaining who program first
  have secondBefore := position_add_remaining who program second
  have firstAfter := position_add_remaining who program firstResult.1
  have secondAfter := position_add_remaining who program secondResult.1
  rw [observed] at firstAfter
  have rank : position who program (ProtocolState.observe who program first) =
      position who program (ProtocolState.observe who program second) := by omega
  have left := recover_recoveryStep who program first firstExcluded firstJoint firstResult
    firstReached firstSurvives
  have right := recover_recoveryStep who program second secondExcluded secondJoint secondResult
    secondReached secondSurvives
  rw [rank, observed, right] at left
  exact Option.some.inj left.symm

end Vegas.SourceProgram.ProtocolView
