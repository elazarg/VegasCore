/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryCommitEntry
import Vegas.Game.CommitRecoveryAttemptDebtPayoff

/-! # Standing failure payoffs from genuine committing source histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Actual commitment syntax supplies the typed block and its fresh context.
An own failed declaration surviving the original close has the exclusion
payoff under arbitrary later continuations, with no supplied block geometry. -/
theorem commitRecovery_failed_commit_attempt_payoff
    (profile future : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (fuel : Nat) (distance : fuel + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point)
    (who : Player) (stopped : setup.commitRecoveryProtocol.History)
    (supported : stopped ∈ (setup.commitRecoveryModel.runBehavioralUntil
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile
      (fun history => history.state.map (fun point => point.publicAddress.2.2) ≠
        some current.publicAddress.2.2) ⟨some current, trace⟩).support)
    (clear : stopped.state.elim False (fun last => last.excluded = current.entryExcluded))
    (recorded : ∃ joint ∈ (setup.recoveryJointRecall stopped.trace).take fuel,
      ∃ move, joint who = some move ∧ move.action.IsFailure)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (final : setup.commitRecoveryProtocol.History)
    (continued : final ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories future stopped).support) :
    setup.commitRecoveryPayoff utility excludedPayoff who final = excludedPayoff who := by
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
  exact setup.commitRecovery_stopped_attempt_failed_payoff profile future remaining suffix boundary
    positive origin current trace entry atEntry who unique stopped supported clear recorded
    utility excludedPayoff final continued

/-- The literal finite remaining window has the same standing-failure payoff.
Its original length and raw word are retained through the actual first close. -/
theorem commitRecovery_failed_commit_window_payoff
    (profile future : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (fuel : Nat) (distance : fuel + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point)
    (who : Player) (stopped : setup.commitRecoveryProtocol.History)
    (supported : stopped ∈ (setup.commitRecoveryModel.runBehavioralFrom profile fuel
      ⟨some current, trace⟩).support)
    (clear : stopped.state.elim False (fun last => last.excluded = current.entryExcluded))
    (recorded : ∃ joint ∈ (setup.recoveryJointRecall stopped.trace).take fuel,
      ∃ move, joint who = some move ∧ move.action.IsFailure)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (final : setup.commitRecoveryProtocol.History)
    (continued : final ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories future stopped).support) :
    setup.commitRecoveryPayoff utility excludedPayoff who final = excludedPayoff who := by
  apply setup.commitRecovery_failed_commit_attempt_payoff profile future current trace committing
    fuel distance who stopped _ clear recorded utility excludedPayoff final continued
  rwa [setup.commitRecovery_run_until_attempt_exit profile fuel current trace committing distance]

end Vegas.SourceProgram.Setup
