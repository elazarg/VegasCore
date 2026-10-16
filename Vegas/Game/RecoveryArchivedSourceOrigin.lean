/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedSavedWord

/-! # Actual archived checkpoints retained in the same genuine source history -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every archive has its actual old typed checkpoint and a genuine source
history prefix into the current source history. All retained conditions concern
existing native records; no source observation or information equality is assumed. -/
def ArchivedSourceOrigins (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (retired : List (RetiredCommitAttempt ((toEventGraph setup.program).withMode mode)))
    (history : setup.commitRecoveryProtocol.History) : Prop :=
  ∀ (index : Nat) (bound : index < retired.length),
    ∃ (state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
      (checkpoint : RecoverySourceCheckpoint setup mode state),
      checkpoint.ArchivedRecall ∧ state.retired = retired.take index ∧
      state.attempt = retired[index].attempt ∧
      state.entry.native.config.history.IsPrefix retired[index].state.config.history ∧
      state.entry.native.config.cut.IsPrefix state.attempt.phase ∧
      checkpoint.refs.Agrees checkpoint.source.state retired[index].state.config.store ∧
      0 < eventCount checkpoint.residual.tail ∧
      ∃ (prior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
          state.entry.excluded state.generation))) (fuel : Nat),
        setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, prior⟩ history

namespace ArchivedSourceOrigins

/-- A genuine later source path retains each original archived source prefix. -/
theorem trans {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {retired : List (RetiredCommitAttempt ((toEventGraph setup.program).withMode mode))}
    {first second : setup.commitRecoveryProtocol.History}
    (origins : ArchivedSourceOrigins setup mode retired first) {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel first second) :
    ArchivedSourceOrigins setup mode retired second := by
  intro index bound
  obtain ⟨state, checkpoint, aligned, archive, attempt, retained, saved, agrees, positive,
    prior, earlier, sourcePath⟩ := origins index bound
  exact ⟨state, checkpoint, aligned, archive, attempt, retained, saved, agrees, positive,
    prior, earlier + fuel, sourcePath.trans reached⟩

/-- The actual newest retired image retains its old checkpoint and the exact
old source prefix, while every earlier archive keeps its original source origin. -/
theorem append {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (prior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      state.entry.excluded state.generation)))
    (origins : ArchivedSourceOrigins setup mode state.retired ⟨_, prior⟩)
    (aligned : checkpoint.ArchivedRecall)
    (record : RetiredCommitAttempt ((toEventGraph setup.program).withMode mode))
    (attempt : state.attempt = record.attempt)
    (retained : state.entry.native.config.history.IsPrefix record.state.config.history)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase)
    (agrees : checkpoint.refs.Agrees checkpoint.source.state record.state.config.store)
    (positive : 0 < eventCount checkpoint.residual.tail)
    {next : setup.commitRecoveryProtocol.History} {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, prior⟩ next) :
    ArchivedSourceOrigins setup mode (state.retired ++ [record]) next := by
  intro index bound
  by_cases earlier : index < state.retired.length
  · obtain ⟨old, source, sourceAligned, archive, oldAttempt, oldRetained, oldSaved, oldAgrees,
      oldPositive, trace, steps, sourcePath⟩ := origins index earlier
    refine ⟨old, source, sourceAligned, ?_, ?_, ?_, oldSaved, ?_, oldPositive,
      trace, steps + fuel, sourcePath.trans reached⟩
    · simpa only [List.take_append_of_le_length earlier.le] using archive
    · simpa only [List.getElem_append_left earlier] using oldAttempt
    · simpa only [List.getElem_append_left earlier] using oldRetained
    · intro name cell selected
      simpa only [List.getElem_append_left earlier] using oldAgrees selected
  · have last : index = state.retired.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst index
    refine ⟨state, checkpoint, aligned, ?_, ?_, ?_, saved, ?_, positive, prior, fuel, reached⟩
    · simp only [List.take_left' rfl]
    · simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] using attempt
    · simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] using retained
    · intro name cell selected
      simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] using agrees selected

end ArchivedSourceOrigins
end Vegas
