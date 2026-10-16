/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptExtraction
import Vegas.Source.CommitRecoveryAttemptReadout

/-! # Success readback at the actual original source attempt stop -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- An actual supported first-attempt stop supplies its typed attempt and the
success marker on the erased closed state, relative to the ORIGINAL saved
exclusions. The actual raw word is retained; no attempt or success premise is
supplied. Earlier current-attempt foreign omissions make the marker false. -/
theorem commitRecovery_stopped_attempt_success
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
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
    (who : Player) (active : who ∉ current.excluded)
    (unique : (Γ.map Prod.fst).Nodup) (values : entry.BindingsHoldValues who)
    (final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralUntil
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile
      (fun history => history.state.map (fun point => point.publicAddress.2.2) ≠
        some current.publicAddress.2.2) ⟨some current, trace⟩).support) :
    ∃ (finished : Config Player L Δ) (after : Finset Player)
      (attempt : block.Attempt entry current.excluded finished after),
      setup.recoveryJointRecall final.trace =
        attempt.joints.reverse ++ setup.recoveryJointRecall trace ∧
      ((current.excluded = current.entryExcluded ∧ attempt.failedOwners = ∅ ∧
          ∀ joint ∈ attempt.joints, ∀ move, joint who = some move → ¬ move.action.IsFailure) ↔
        final.state.elim False (fun stopped => stopped.excluded = current.entryExcluded ∧
          ProtocolState.BindingsHoldValues who setup.program stopped.eraseHistory.point)) := by
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
  obtain ⟨target, joints, addresses, state, length, path, _traceLength, word, _signals⟩ :=
    setup.commitRecovery_stopped_attempt_instructions profile initial block.length current trace
      committing distance final supported
  obtain ⟨finished, after, attempt, attemptWord, monotone, targetEq⟩ :=
    block.attempt_of_instructions initial suffix lift origin entry current target joints addresses
      atEntry savedCommit (Nat.le_of_eq endpoint) positive path length
  refine ⟨finished, after, attempt, ?_, ?_⟩
  · rw [attemptWord]
    exact word
  · rw [state]
    change _ ↔ target.excluded = current.entryExcluded ∧
      ProtocolState.BindingsHoldValues who setup.program target.eraseHistory.point
    have erase : ProtocolState.BindingsHoldValues who setup.program target.eraseHistory.point ↔
        ProtocolState.BindingsHoldValues who setup.program target.point :=
      ProtocolState.bindingsHoldValues_withHistory who setup.program target.point _
    rw [erase]
    have readout : (target.excluded = current.entryExcluded ∧
        ProtocolState.BindingsHoldValues who setup.program target.point) ↔
        (after = current.entryExcluded ∧ finished.BindingsHoldValues who) := by
      rw [targetEq]
      let pending := current.install
        (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), after) monotone
      change (pending.close.excluded = pending.entryExcluded ∧
        ProtocolState.BindingsHoldValues who setup.program pending.close.point) ↔ _
      rw [pending.close_success_readout who]
      change (after = current.entryExcluded ∧ ProtocolState.BindingsHoldValues who setup.program
        (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)))) ↔ _
      rw [origin.bindingsHoldValues_lift, block.bindingsHoldValues_liftPoint,
        ProtocolState.bindingsHoldValues_entry]
    rw [readout]
    by_cases clear : current.excluded = current.entryExcluded
    · have typed := attempt.no_failure_iff_completed_readout who unique values active
      simpa only [← clear, true_and, Config.BindingsHoldValues] using typed
    · have afterDifferent : after ≠ current.entryExcluded := by
        intro same
        apply clear
        exact Finset.Subset.antisymm (same ▸ attempt.excluded_subset) current.entered
      exact iff_of_false (fun holds => clear holds.1) (fun holds => afterDifferent holds.1)

end Vegas.SourceProgram.Setup
