/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptDebt
import Vegas.Source.CommitRecoveryAttemptExtraction
import Vegas.Source.CommitRecoveryAttemptReadout
import Vegas.Game.CommitRecoveryDebtPayoff

/-! # Actual no-reset attempt failures have the permanent exclusion payoff

The failed raw declaration is read from the original stopped source word.
The typed attempt and clean close are extracted from that same original run.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- An own failed raw declaration that stands at the original attempt exit
forces the exclusion payoff under EVERY later continuation, even through
future retries. No terminal payoff or checkpoint debt is assumed. -/
theorem commitRecovery_stopped_attempt_failed_payoff
    (profile future : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (boundary : IsCommitBoundary suffix) (positive : 0 < block.length)
    {lift : SourceProgram.ProtocolState (block.prepend suffix) →
      SourceProgram.ProtocolState setup.program}
    (origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (entry : Config Player L Γ)
    (atEntry : current.point = lift (ProtocolState.entry (block.prepend suffix) entry))
    (who : Player) (unique : (Γ.map Prod.fst).Nodup)
    (stopped : setup.commitRecoveryProtocol.History)
    (supported : stopped ∈ (setup.commitRecoveryModel.runBehavioralUntil
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile
      (fun history => history.state.map (fun point => point.publicAddress.2.2) ≠
        some current.publicAddress.2.2) ⟨some current, trace⟩).support)
    (clear : stopped.state.elim False (fun last => last.excluded = current.entryExcluded))
    (recorded : ∃ joint ∈ (setup.recoveryJointRecall stopped.trace).take block.length,
      ∃ move, joint who = some move ∧ move.action.IsFailure)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (final : setup.commitRecoveryProtocol.History)
    (continued : final ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories future stopped).support) :
    setup.commitRecoveryPayoff utility excludedPayoff who final = excludedPayoff who := by
  classical
  have committing : ProtocolState.atCommit setup.program current.point = true := by
    rw [atEntry, origin.atCommit_lift]
    cases block with
    | nil => cases positive
    | commit => rfl
  have frontier := setup.commitRecovery_blockFrontier trace
  have savedCommit : ProtocolState.atCommit setup.program current.saved = true := by
    rcases frontier with ⟨saved, _live, _end⟩ | same
    · exact saved
    · rwa [same]
  have sameEnd : ProtocolState.commitEnd setup.program current.point =
      ProtocolState.commitEnd setup.program current.saved := by
    rcases frontier with ⟨_saved, _live, sameEnd⟩ | same
    · exact sameEnd
    · rw [same]
  have endpoint : ProtocolState.commitEnd setup.program current.saved =
      instructionCount suffix := by
    rw [← sameEnd, atEntry, origin.commitEnd_lift, block.commitEnd_entry_prepend suffix boundary]
  have distance : block.length + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point := by
    rw [endpoint, atEntry, origin.remaining_lift, ProtocolState.remaining_entry,
      block.instructionCount_prepend]
  let initial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  obtain ⟨last, joints, addresses, state, length, path, _traceLength, word, _signals⟩ :=
    setup.commitRecovery_stopped_attempt_instructions profile initial block.length current trace
      committing distance stopped supported
  obtain ⟨finished, after, attempt, attemptWord, monotone, lastEq⟩ :=
    block.attempt_of_instructions initial suffix lift origin entry current last joints addresses
      atEntry savedCommit (Nat.le_of_eq endpoint) positive path length
  have actualWord : (setup.recoveryJointRecall stopped.trace).take block.length =
      attempt.joints.reverse := by
    have reversedLength : attempt.joints.reverse.length = block.length :=
      List.length_reverse.trans attempt.joints_length
    rw [word, ← attemptWord, ← reversedLength, List.take_left]
  rw [actualWord] at recorded
  obtain ⟨joint, member, move, selected, failed⟩ := recorded
  have failedBinding := attempt.failedBinding_of_failed_joint who unique joint
    (List.mem_reverse.mp member) move selected failed
  have live : ProtocolState.OwesFailure who setup.program
      (lift (block.liftPoint suffix (ProtocolState.entry suffix finished))) :=
    Or.inr (origin.failedBinding_lift who _
      (block.failedBinding_liftPoint suffix who _
        (ProtocolState.failedBinding_entry suffix finished failedBinding)))
  let pending := current.install
    (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), after) monotone
  have completed : pending.Finished := by
    refine ⟨savedCommit, ?_⟩
    change ProtocolState.remaining setup.program
      (lift (block.liftPoint suffix (ProtocolState.entry suffix finished))) =
        ProtocolState.commitEnd setup.program current.saved
    rw [origin.remaining_lift, block.liftPoint_remaining, ProtocolState.remaining_entry, endpoint]
  have noFailure : ¬ pending.NewFailure := by
    have equal : after = current.entryExcluded := by
      rw [state, lastEq] at clear
      simpa only [Option.elim_some, CommitRecoveryState.close_excluded,
        CommitRecoveryState.install] using clear
    simp only [CommitRecoveryState.NewFailure, pending, CommitRecoveryState.install, equal,
      Finset.sdiff_self, Finset.not_nonempty_empty, not_false_eq_true]
  have owed := pending.close_checkpointed_owesFailure who completed noFailure live
  apply setup.commitRecovery_terminal_payoff_of_checkpointed_debt utility excludedPayoff who
    future stopped last state (Or.inr ?_) final continued
  rw [lastEq]
  exact owed

end Vegas.SourceProgram.Setup
