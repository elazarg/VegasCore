/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptOmissions
import Vegas.Game.CommitRecoveryCommitFailure

/-! # Original raw-word success is the actual erased first-close readout -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- The actual original window's no-omission/no-own-failed-action event is
read from the erased stopped state. The typed attempt and its geometry are
derived internally from the genuine committing history. -/
theorem commitRecovery_commit_window_success_iff
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (fuel : Nat) (distance : fuel + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point)
    (who : Player) (active : who ∉ current.excluded)
    (values : ProtocolState.BindingsHoldValues who setup.program current.point)
    (stopped : setup.commitRecoveryProtocol.History)
    (supported : stopped ∈ (setup.commitRecoveryModel.runBehavioralFrom profile fuel
      ⟨some current, trace⟩).support) :
    (current.excluded = current.entryExcluded ∧
      (∀ joint ∈ (setup.recoveryJointRecall stopped.trace).take fuel, ∀ owner,
        CommitRecoveryMove.missed (joint owner) = false) ∧
      (∀ joint ∈ (setup.recoveryJointRecall stopped.trace).take fuel, ∀ move,
        joint who = some move → ¬ move.action.IsFailure)) ↔
      stopped.state.elim False (fun last => last.excluded = current.entryExcluded ∧
        ProtocolState.BindingsHoldValues who setup.program last.eraseHistory.point) := by
  obtain ⟨Γ, O, name, owner, payload, fresh, guard, next, lift, entry, origin, atEntry, unique⟩ :=
    ProtocolState.exists_committing_entry setup.program current.point setup.namesNodup committing
  obtain ⟨Δ, P, suffix, block, reconstruct, boundary⟩ := commitPhase next
  cases reconstruct
  let remaining : CommitPrefix Γ O Δ P := .commit name owner fresh guard block
  have positive : 0 < remaining.length := Nat.zero_lt_succ _
  have endpoint : ProtocolState.commitEnd setup.program current.saved =
      instructionCount suffix := by
    have frontier := setup.commitRecovery_blockFrontier trace
    have sameEnd : ProtocolState.commitEnd setup.program current.point =
        ProtocolState.commitEnd setup.program current.saved := by
      rcases frontier with ⟨_saved, _live, sameEnd⟩ | same
      · exact sameEnd
      · rw [same]
    rw [← sameEnd, atEntry, origin.commitEnd_lift]
    exact remaining.commitEnd_entry_prepend suffix boundary entry
  have blockDistance : remaining.length + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point := by
    rw [endpoint, atEntry, origin.remaining_lift, ProtocolState.remaining_entry]
    exact (remaining.instructionCount_prepend suffix).symm
  have sameFuel : fuel = remaining.length := by omega
  subst fuel
  have initial : entry.BindingsHoldValues who := by
    rw [atEntry, origin.bindingsHoldValues_lift, ProtocolState.bindingsHoldValues_entry] at values
    exact values
  have stoppedSupport : stopped ∈ (setup.commitRecoveryModel.runBehavioralUntil
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile
      (fun history => history.state.map (fun point => point.publicAddress.2.2) ≠
        some current.publicAddress.2.2) ⟨some current, trace⟩).support := by
    rwa [setup.commitRecovery_run_until_attempt_exit profile remaining.length current trace
      committing blockDistance]
  obtain ⟨finished, after, attempt, word, success⟩ :=
    setup.commitRecovery_stopped_attempt_success profile remaining suffix boundary positive origin
      current trace entry atEntry who active unique initial stopped stoppedSupport
  have actualWord : (setup.recoveryJointRecall stopped.trace).take remaining.length =
      attempt.joints.reverse := by
    have reversedLength : attempt.joints.reverse.length = remaining.length :=
      List.length_reverse.trans attempt.joints_length
    rw [word, ← reversedLength, List.take_left]
  rw [actualWord]
  simpa only [List.mem_reverse, ← attempt.failedOwners_eq_empty_iff_no_missed] using success

end Vegas.SourceProgram.Setup
