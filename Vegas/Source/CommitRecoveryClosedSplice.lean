/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryStateSplice

/-! # Owner substitution through actual source attempt closure

The original saved checkpoint and permanent own-action histories are combined
before the existing clean, retry or exhausted close operation is applied.
-/

noncomputable section

namespace Vegas.SourceProgram.CommitRecoveryState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- Substitute one owner's original typed stores and permanent action words,
retaining the other world's actual public exclusion and attempt control. -/
def splice (focal : Player) (mine others : CommitRecoveryState program) :
    CommitRecoveryState program where
  point := ProtocolState.splice focal program mine.point others.point
  saved := ProtocolState.splice focal program mine.saved others.saved
  excluded := others.excluded
  entryExcluded := others.entryExcluded
  generation := others.generation
  entered := others.entered

/-- A closed source checkpoint combines the same original entry points. -/
theorem splice_atPoint (focal : Player) (mine others : ProtocolState program)
    (leftExcluded rightExcluded : Finset Player) (leftGeneration rightGeneration : Nat) :
    splice focal (atPoint mine leftExcluded leftGeneration)
        (atPoint others rightExcluded rightGeneration) =
      atPoint (ProtocolState.splice focal program mine others) rightExcluded rightGeneration := rfl

/-- Owner substitution preserves the actual structural control of the second world. -/
theorem splice_metadata_eq_others (focal : Player) (mine others : CommitRecoveryState program)
    (metadata : mine.MetadataEq others) : (splice focal mine others).MetadataEq others := by
  exact ⟨ProtocolState.splice_metadata_eq_others focal program _ _ metadata.1,
    ProtocolState.splice_metadata_eq_others focal program _ _ metadata.2.1, rfl, rfl, rfl⟩

/-- Restoring a failed attempt retains the combined permanent original own words. -/
theorem splice_restored (focal : Player) (mine others : CommitRecoveryState program)
    (metadata : mine.MetadataEq others) :
    ProtocolState.splice focal program mine.restored others.restored =
      (splice focal mine others).restored := by
  unfold restored
  rw [ProtocolState.splice_withHistory focal program _ _ metadata.2.1]
  change ProtocolState.withHistory program
      (ProtocolState.splice focal program mine.saved others.saved) _ =
    ProtocolState.withHistory program (ProtocolState.splice focal program mine.saved others.saved)
        (ProtocolState.history program (ProtocolState.splice focal program mine.point others.point))
  rw [ProtocolState.history_splice focal program _ _ metadata.1]

/-- A genuine retry commutes with substitution, including the new attempt generation. -/
theorem splice_retry (focal : Player) (mine others : CommitRecoveryState program)
    (metadata : mine.MetadataEq others) :
    splice focal mine.retry others.retry = (splice focal mine others).retry := by
  simp only [retry, splice_atPoint]
  rw [splice_restored focal mine others metadata]
  rfl

/-- Exhausting an attempt combines the original automatically filled checkpoint. -/
theorem splice_exhausted (focal : Player) (mine others : CommitRecoveryState program)
    (metadata : mine.MetadataEq others) :
    splice focal mine.exhausted others.exhausted = (splice focal mine others).exhausted := by
  have restoredMetadata := ProtocolState.MetadataEq.withHistory program mine.saved others.saved
    metadata.2.1 (ProtocolState.history program mine.point)
      (ProtocolState.history program others.point)
  change ProtocolState.MetadataEq program mine.restored others.restored at restoredMetadata
  simp only [exhausted, splice_atPoint]
  rw [ProtocolState.splice_automaticCommitBlock focal program _ _ restoredMetadata,
    splice_restored focal mine others metadata]
  rfl

private theorem metadata_close_tests (mine others : CommitRecoveryState program)
    (metadata : mine.MetadataEq others) :
    mine.Finished = others.Finished ∧ mine.NewFailure = others.NewFailure ∧
      mine.Survives = others.Survives ∧
      ProtocolState.atCommit program mine.saved = ProtocolState.atCommit program others.saved := by
  have point := ProtocolState.MetadataEq.controls program mine.point others.point metadata.1
  have saved := ProtocolState.MetadataEq.controls program mine.saved others.saved metadata.2.1
  refine ⟨?_, ?_, ?_, saved.2.1⟩
  · unfold Finished
    rw [saved.2.1, point.1, saved.2.2.1]
  · unfold NewFailure
    rw [metadata.2.2.1, metadata.2.2.2.1]
  · unfold Survives
    rw [saved.2.2.2, metadata.2.2.1]

/-- The actual original closure dispatcher commutes with owner substitution.
Clean progress, retry with remembered retired choices, exhausted automatic
completion and unfinished prefixes are all retained by the same operation. -/
theorem splice_close (focal : Player) (mine others : CommitRecoveryState program)
    (metadata : mine.MetadataEq others) :
    splice focal mine.close others.close = (splice focal mine others).close := by
  have leftTests := metadata_close_tests mine others metadata
  have mixedTests := metadata_close_tests (splice focal mine others) others
    (splice_metadata_eq_others focal mine others metadata)
  unfold close
  rw [leftTests.1, mixedTests.1, leftTests.2.1, mixedTests.2.1,
    leftTests.2.2.1, mixedTests.2.2.1, leftTests.2.2.2, mixedTests.2.2.2]
  by_cases finished : others.Finished
  · simp only [finished, ↓reduceIte]
    by_cases failed : others.NewFailure
    · simp only [failed, ↓reduceIte]
      by_cases survivor : others.Survives
      · simp only [survivor, ↓reduceIte]
        exact splice_retry focal mine others metadata
      · simp only [survivor, ↓reduceIte]
        exact splice_exhausted focal mine others metadata
    · simp only [failed, ↓reduceIte]
      rfl
  · simp only [finished, ↓reduceIte]
    split <;> rfl

end Vegas.SourceProgram.CommitRecoveryState
