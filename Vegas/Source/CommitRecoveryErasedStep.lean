/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasure

/-! # Actual source transitions after erasing remembered words

The original typed stores, obligations, private input tuples, exclusions and
chance laws are unchanged. These identities concern the existing recovery
instruction kernel and its actual retry/exhaustion dispatcher.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

@[simp] theorem withHistory_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (past : History Player L) :
    withHistory program (entry program config) past = entry program {config with history := past} :=
  by cases program <;> rfl

/-- Source control depends on the actual cursor, never the retired word. -/
theorem withHistory_control : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    actor program (withHistory program point past) = actor program point ∧
      atCommit program (withHistory program point past) = atCommit program point ∧
      commitOwners program (withHistory program point past) = commitOwners program point
  | _, _, .ret _, _, _ => ⟨rfl, rfl, rfl⟩
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => exact ⟨rfl, rfl, rfl⟩
      | inr point => exact withHistory_control next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl _ => exact ⟨rfl, rfl, rfl⟩
      | inr point => exact withHistory_control next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => exact ⟨rfl, rfl, rfl⟩
      | inr point => exact withHistory_control next point past

/-- Automatic excluded-owner completion commutes with replacing memory. -/
theorem withHistory_automaticCommitBlock :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (past : History Player L),
      automaticCommitBlock program (withHistory program point past) =
        withHistory program (automaticCommitBlock program point) past
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact congrArg Sum.inr (withHistory_automaticCommitBlock next point past)
  | _, _, .commit name owner _ _ next, point, past => by
      cases point with
      | inl config =>
          simp only [automaticCommitBlock, withHistory, Sum.elim_inl, Sum.elim_inr]
          rw [← withHistory_automaticCommitBlock next
            (entry next (automaticCommit name owner _ config)) past, withHistory_entry]
          rfl
      | inr point => exact congrArg Sum.inr (withHistory_automaticCommitBlock next point past)
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact congrArg Sum.inr (withHistory_automaticCommitBlock next point past)

/-- The actual raw source kernel has the same full semantic/exclusion law
after removing only its remembered words. This includes rejected openings,
automatic excluded actions, public samples and accepted failed bindings. -/
theorem recoveryStep_eraseHistory :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
      (recoveryStep program (withHistory program point (fun _ => [])) excluded joint).map
          (fun result => (withHistory program result.1 (fun _ => []), result.2)) =
        (recoveryStep program point excluded joint).map
          (fun result => (withHistory program result.1 (fun _ => []), result.2))
  | _, _, .ret _, _, _, _ => by
      simp only [recoveryStep, PMF.pure_map, withHistory_withHistory]
  | _, _, .sample name fresh law next, point, excluded, joint => by
      cases point with
      | inl config =>
          simp only [recoveryStep, withHistory, Sum.elim_inl, PMF.map_comp]
          apply congrArg (fun f => (L.evalDist law (sourcePublicEnv config.state)).map f)
          funext value
          simp only [Function.comp_apply, Sum.elim_inr, withHistory_entry]
          rfl
      | inr point =>
          simpa only [recoveryStep, withHistory, Sum.elim_inr, PMF.map_comp, Function.comp_def]
            using congrArg (PMF.map (fun result => (Sum.inr result.1, result.2)))
              (recoveryStep_eraseHistory next point excluded joint)
  | _, _, .commit name owner fresh guard next, point, excluded, joint => by
      cases point with
      | inl config =>
          simp only [recoveryStep, withHistory, Sum.elim_inl]
          split <;>
            simp only [PMF.pure_map, Sum.elim_inr, withHistory_entry,
              automaticCommit, commitSuccessor]
      | inr point =>
          simpa only [recoveryStep, withHistory, Sum.elim_inr, PMF.map_comp, Function.comp_def]
            using congrArg (PMF.map (fun result => (Sum.inr result.1, result.2)))
              (recoveryStep_eraseHistory next point excluded joint)
  | _, _, .reveal published owner name fresh source unresolved next, point, excluded, joint => by
      cases point with
      | inl config =>
          simp only [recoveryStep, withHistory, Sum.elim_inl, PMF.pure_map]
          split <;>
            simp only [Sum.elim_inr, withHistory_entry, revealSuccessor]
      | inr point =>
          simpa only [recoveryStep, withHistory, Sum.elim_inr, PMF.map_comp, Function.comp_def]
            using congrArg (PMF.map (fun result => (Sum.inr result.1, result.2)))
              (recoveryStep_eraseHistory next point excluded joint)

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- Forget remembered words in both source cursors, retaining every semantic
field of the original saved and live configurations. -/
def eraseHistory (state : CommitRecoveryState program) : CommitRecoveryState program :=
  {state with
    point := ProtocolState.withHistory program state.point (fun _ => [])
    saved := ProtocolState.withHistory program state.saved (fun _ => [])}

@[simp] theorem eraseHistory_idempotent (state : CommitRecoveryState program) :
    state.eraseHistory.eraseHistory = state.eraseHistory := by
  simp only [eraseHistory, ProtocolState.withHistory_withHistory]

/-- A real retry erases the same semantic attempted fields on either side;
retaining the old private word does not affect this identity. -/
theorem eraseHistory_retry (state : CommitRecoveryState program) :
    state.retry.eraseHistory = state.eraseHistory.retry := by
  simp only [eraseHistory, retry, atPoint, restored, ProtocolState.withHistory_withHistory,
    ProtocolState.history_withHistory]

/-- Exhausted restore also commutes; it is not identified with a retry. -/
theorem eraseHistory_exhausted (state : CommitRecoveryState program) :
    state.exhausted.eraseHistory = state.eraseHistory.exhausted := by
  simp only [eraseHistory, exhausted, atPoint, restored, ProtocolState.withHistory_withHistory,
    ProtocolState.history_withHistory, ProtocolState.withHistory_automaticCommitBlock]

/-- The existing dispatcher takes the same clean/retry/exhausted branch after
memory erasure. No desired endpoint or success event is assumed. -/
theorem eraseHistory_close (state : CommitRecoveryState program) :
    state.close.eraseHistory = state.eraseHistory.close := by
  have savedControl := ProtocolState.withHistory_control program state.saved (fun _ => [])
  have finished : state.eraseHistory.Finished ↔ state.Finished := by
    simp only [Finished, eraseHistory, savedControl.2.1, ProtocolState.remaining_withHistory,
      ProtocolState.commitEnd_withHistory]
  have failed : state.eraseHistory.NewFailure ↔ state.NewFailure := Iff.rfl
  have survives : state.eraseHistory.Survives ↔ state.Survives := by
    simp only [Survives, eraseHistory, savedControl.2.2]
  by_cases complete : state.Finished
  · have complete' := finished.mpr complete
    by_cases failure : state.NewFailure
    · have failure' := failed.mpr failure
      by_cases survivor : state.Survives
      · have survivor' := survives.mpr survivor
        simp only [close, complete, complete', failure, failure', survivor, survivor', ↓reduceIte]
        exact state.eraseHistory_retry
      · have survivor' : ¬ state.eraseHistory.Survives := fun yes => survivor (survives.mp yes)
        simp only [close, complete, complete', failure, failure', survivor, survivor', ↓reduceIte]
        exact state.eraseHistory_exhausted
    · have failure' : ¬ state.eraseHistory.NewFailure := fun yes => failure (failed.mp yes)
      simp only [close, complete, complete', failure, failure', ↓reduceIte]
      rfl
  · have complete' : ¬ state.eraseHistory.Finished := fun yes => complete (finished.mp yes)
    by_cases committing : ProtocolState.atCommit program state.saved = true
    · have committing' : ProtocolState.atCommit program state.eraseHistory.saved = true := by
        simpa only [eraseHistory, savedControl.2.1] using committing
      simp only [close, complete, complete', committing, committing', ↓reduceIte]
    · have committing' : ProtocolState.atCommit program state.eraseHistory.saved ≠ true := by
        simpa only [eraseHistory, savedControl.2.1] using committing
      simp only [close, complete, complete', committing, committing', ↓reduceIte]
      rfl

/-- Installing the original result commutes with erasing remembered words.
The original result's exclusion-monotonicity proof is retained. -/
theorem eraseHistory_install (state : CommitRecoveryState program)
    (result : ProtocolState program × Finset Player) (monotone : state.excluded ⊆ result.2) :
    (state.install result monotone).eraseHistory =
      state.eraseHistory.install
        (ProtocolState.withHistory program result.1 (fun _ => []), result.2) monotone := rfl

/-- The existing complete source step, including its actual close dispatcher,
has the same semantic and exclusion law after history erasure. -/
theorem step_eraseHistory (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) :
    (state.eraseHistory.step joint).map eraseHistory = (state.step joint).map eraseHistory := by
  classical
  let eraseResult := fun result : ProtocolState program × Finset Player =>
    (ProtocolState.withHistory program result.1 (fun _ => []), result.2)
  let finish := fun (before : CommitRecoveryState program)
      (result : ProtocolState program × Finset Player) =>
    if monotone : before.excluded ⊆ result.2 then
      (before.install result monotone).close.eraseHistory
    else before.eraseHistory
  have expressed (before : CommitRecoveryState program) :
      (before.step joint).map eraseHistory =
        (ProtocolState.recoveryStep program before.point before.excluded joint).map
          (finish before) := by
    let raw := ProtocolState.recoveryStep program before.point before.excluded joint
    let monotone := fun result (supported : result ∈ raw.support) =>
      ProtocolState.recoveryStep_excluded_monotone program before.point before.excluded joint
        result supported
    change ((pmfToSubtype raw monotone).map
      (fun result => (before.install result.1 result.2).close)).map eraseHistory = _
    rw [PMF.map_comp]
    calc
      _ = (pmfToSubtype raw monotone).map (fun result => finish before result.1) := by
        congr 1
        funext result
        simp only [Function.comp_apply, finish, dite_eq_left result.2]
      _ = _ := map_pmfToSubtype raw monotone (finish before)
  have finished (before : CommitRecoveryState program)
      (result : ProtocolState program × Finset Player) :
      finish before.eraseHistory (eraseResult result) = finish before result := by
    dsimp only [finish]
    change (if monotone : before.excluded ⊆ result.2 then _ else _) = _
    split
    · next monotone =>
        rw [← before.eraseHistory_install result monotone, ← eraseHistory_close,
          eraseHistory_idempotent]
    · exact eraseHistory_idempotent before
  rw [expressed, expressed]
  change (ProtocolState.recoveryStep program
    (ProtocolState.withHistory program state.point (fun _ => [])) state.excluded joint).map
      (finish state.eraseHistory) = _
  calc
    _ = ((ProtocolState.recoveryStep program
        (ProtocolState.withHistory program state.point (fun _ => [])) state.excluded joint).map
          eraseResult).map (finish state.eraseHistory) := by
      rw [PMF.map_comp]
      congr 1
      funext result
      simpa only [eraseHistory_idempotent, Function.comp_apply] using
        (finished state.eraseHistory result).symm
    _ = ((ProtocolState.recoveryStep program state.point state.excluded joint).map
        eraseResult).map (finish state.eraseHistory) := by
      rw [ProtocolState.recoveryStep_eraseHistory]
    _ = _ := by
      rw [PMF.map_comp]
      congr 1
      funext result
      exact finished state result

end CommitRecoveryState
end Vegas.SourceProgram
