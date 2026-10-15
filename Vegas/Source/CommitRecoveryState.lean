/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryStep

/-! # Automatic source phase closure and permanent exclusion -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- Source recovery retains the entry semantic frontier and all private actions
of its current attempt. The retry generation is global across program phases. -/
structure CommitRecoveryState (program : SourceProgram Player L Γ O) where
  point : ProtocolState program
  saved : ProtocolState program
  excluded : Finset Player
  entryExcluded : Finset Player
  generation : Nat
  entered : entryExcluded ⊆ excluded

namespace CommitRecoveryState

def atPoint (point : ProtocolState program) (excluded : Finset Player) (generation : Nat) :
    CommitRecoveryState program :=
  ⟨point, point, excluded, excluded, generation, Finset.Subset.refl _⟩

def Finished (state : CommitRecoveryState program) : Prop :=
  ProtocolState.atCommit program state.saved = true ∧
    ProtocolState.remaining program state.point = ProtocolState.commitEnd program state.saved

def NewFailure (state : CommitRecoveryState program) : Prop :=
  (state.excluded \ state.entryExcluded).Nonempty

def Survives (state : CommitRecoveryState program) : Prop :=
  (ProtocolState.commitOwners program state.saved \ state.excluded).Nonempty

def restored (state : CommitRecoveryState program) : ProtocolState program :=
  ProtocolState.withHistory program state.saved (ProtocolState.history program state.point)

def retry (state : CommitRecoveryState program) : CommitRecoveryState program :=
  atPoint state.restored state.excluded (state.generation + 1)

def exhausted (state : CommitRecoveryState program) : CommitRecoveryState program :=
  atPoint (ProtocolState.automaticCommitBlock program state.restored) state.excluded
    state.generation

/-- Close a maximal commitment block at its boundary. Only new actual binding
omissions can reset it, and no excluded owner is retried. -/
def close (state : CommitRecoveryState program) : CommitRecoveryState program := by
  classical
  exact if state.Finished then
    if state.NewFailure then
      if state.Survives then state.retry else state.exhausted
    else atPoint state.point state.excluded state.generation
  else if ProtocolState.atCommit program state.saved then state
    else atPoint state.point state.excluded state.generation

theorem close_of_retry (state : CommitRecoveryState program)
    (finished : state.Finished) (failed : state.NewFailure) (survives : state.Survives) :
    state.close = state.retry := by simp only [close, finished, failed, survives, ↓reduceIte]

theorem close_of_exhausted (state : CommitRecoveryState program)
    (finished : state.Finished) (failed : state.NewFailure) (noSurvivor : ¬ state.Survives) :
    state.close = state.exhausted := by
  simp only [close, finished, failed, noSurvivor, ↓reduceIte]

@[simp] theorem close_excluded (state : CommitRecoveryState program) :
    state.close.excluded = state.excluded := by
  unfold close
  split
  · split
    · split <;> rfl
    · rfl
  · split <;> rfl

@[simp] theorem close_history (state : CommitRecoveryState program) :
    ProtocolState.history program state.close.point =
      ProtocolState.history program state.point := by
  unfold close
  split
  · split
    · split
      · exact ProtocolState.history_withHistory _ _ _
      · exact (ProtocolState.automaticCommitBlock_history _ _).trans
          (ProtocolState.history_withHistory _ _ _)
    · rfl
  · split <;> rfl

theorem retry_restore (state : CommitRecoveryState program) :
    ProtocolState.withHistory program state.retry.point
      (ProtocolState.history program state.saved) = state.saved := by
  simp only [retry, atPoint, restored, ProtocolState.withHistory_withHistory,
    ProtocolState.withHistory_history]

theorem entryExcluded_close (state : CommitRecoveryState program) :
    state.entryExcluded ⊆ state.close.entryExcluded := by
  unfold close
  split
  · split
    · split <;> exact state.entered
    · exact state.entered
  · split
    · exact Finset.Subset.refl _
    · exact state.entered

theorem retry_entry_card (state : CommitRecoveryState program) (failed : state.NewFailure) :
    state.entryExcluded.card + 1 ≤ state.retry.entryExcluded.card := by
  obtain ⟨who, member⟩ := failed
  have strict : state.entryExcluded ⊂ state.excluded :=
    Finset.ssubset_iff_subset_ne.mpr ⟨state.entered, fun same =>
      (Finset.mem_sdiff.mp member).2 (same.symm ▸ (Finset.mem_sdiff.mp member).1)⟩
  exact Finset.card_lt_card strict

theorem close_generation_bound (state : CommitRecoveryState program)
    (bound : state.generation ≤ state.entryExcluded.card) :
    state.close.generation ≤ state.close.entryExcluded.card := by
  have enlarged := bound.trans (Finset.card_le_card state.entered)
  unfold close
  split
  · split
    · next failed =>
      split
      · have increased := state.retry_entry_card failed
        change state.generation + 1 ≤ state.retry.entryExcluded.card
        omega
      · exact enlarged
    · exact enlarged
  · split
    · exact bound
    · exact enlarged

/-- Install one actual source instruction before any automatic phase close. -/
def install (state : CommitRecoveryState program) (result : ProtocolState program × Finset Player)
    (monotone : state.excluded ⊆ result.2) : CommitRecoveryState program where
  point := result.1
  saved := state.saved
  excluded := result.2
  entryExcluded := state.entryExcluded
  generation := state.generation
  entered := state.entered.trans monotone

def step (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) : PMF (CommitRecoveryState program) :=
  (pmfToSubtype (ProtocolState.recoveryStep program state.point state.excluded joint)
    (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
      state.excluded joint result supported)).map fun result =>
        (state.install result.1 result.2).close

theorem step_excluded_monotone (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) : state.excluded ⊆ next.excluded := by
  obtain ⟨result, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  rw [close_excluded]
  exact result.2

theorem step_generation_bound (state : CommitRecoveryState program)
    (bound : state.generation ≤ state.entryExcluded.card)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) :
    next.generation ≤ next.entryExcluded.card := by
  obtain ⟨result, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact (state.install result.1 result.2).close_generation_bound bound

/-- Closing without a retry never increases the remaining source rank. -/
theorem close_remaining_le (state : CommitRecoveryState program)
    (notRetry : ¬ (state.Finished ∧ state.NewFailure ∧ state.Survives)) :
    ProtocolState.remaining program state.close.point ≤
      ProtocolState.remaining program state.point := by
  unfold close
  split
  · next finished =>
    split
    · next failed =>
      split
      · next survives => exact (notRetry ⟨finished, failed, survives⟩).elim
      · simp only [exhausted, atPoint, ProtocolState.automaticCommitBlock_remaining, restored]
        rw [ProtocolState.commitEnd_withHistory, ← finished.2]
    · exact le_rfl
  · split <;> exact le_rfl

/-- Entry exclusions pay for retries; the remaining instruction rank pays for
every other source step. -/
def potential [Fintype Player] (state : CommitRecoveryState program) : Nat :=
  (Fintype.card Player - state.entryExcluded.card) * (instructionCount program + 1) +
    ProtocolState.remaining program state.point

theorem step_potential_lt [Fintype Player] (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (running : ¬ ProtocolState.terminal program state.point)
    (supported : next ∈ (state.step joint).support) : next.potential < state.potential := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have rawMember : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have consumed := ProtocolState.recoveryStep_remaining program state.point state.excluded joint
    result.1 running rawMember
  let after := state.install result.1 result.2
  change after.close.potential < state.potential
  have beforeCard := Finset.card_le_univ (s := state.entryExcluded)
  have afterCard := Finset.card_le_univ (s := after.excluded)
  by_cases retries : after.Finished ∧ after.NewFailure ∧ after.Survives
  · rw [close_of_retry after retries.1 retries.2.1 retries.2.2]
    have increased := after.retry_entry_card retries.2.1
    have budget : Fintype.card Player - after.retry.entryExcluded.card + 1 ≤
        Fintype.card Player - state.entryExcluded.card := by
      change Fintype.card Player - after.excluded.card + 1 ≤
        Fintype.card Player - state.entryExcluded.card
      change state.entryExcluded.card + 1 ≤ after.excluded.card at increased
      change after.excluded.card ≤ Fintype.card Player at afterCard
      omega
    have scaled := Nat.mul_le_mul_right (instructionCount program + 1) budget
    have bound := ProtocolState.remaining_le_instructionCount program after.retry.point
    dsimp only [potential]
    nlinarith
  · have entries := Finset.card_le_card after.entryExcluded_close
    have budget : Fintype.card Player - after.close.entryExcluded.card ≤
        Fintype.card Player - state.entryExcluded.card := by
      change state.entryExcluded.card ≤ after.close.entryExcluded.card at entries
      omega
    have scaled := Nat.mul_le_mul_right (instructionCount program + 1) budget
    have rank := after.close_remaining_le retries
    change ProtocolState.remaining program result.1.1 + 1 =
      ProtocolState.remaining program state.point at consumed
    change ProtocolState.remaining program after.close.point ≤
      ProtocolState.remaining program result.1.1 at rank
    dsimp only [potential]
    omega

end CommitRecoveryState
end Vegas.SourceProgram
