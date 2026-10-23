/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryInstructions
import Vegas.Source.CommitRecoveryDebt

/-! # Failed own bindings read from a completed original attempt

Actual typed attempts retain their original raw joint word. Their surviving
owner's successful cells distinguish accepted failures without inspecting guards.
-/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix.Attempt

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
  {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
  {after : Finset Player}

/-- No instruction of an original commitment attempt can remove an earlier
failed binding. A restore is a separate operation after this attempt. -/
theorem preserves_failedBinding (attempt : block.Attempt entry excluded finished after)
    (who : Player) (failed : entry.FailedBinding who O) : finished.FailedBinding who P := by
  induction attempt with
  | nil => exact failed
  | @active _ _ _ _ _ _ _ fresh guard _ _ _ _ _ _ choice _ _ _ ih =>
      exact ih (failed.commit fresh guard choice)
  | @excluded _ _ _ _ _ _ _ fresh _ _ _ _ _ _ _ _ ih =>
      exact ih (failed.automaticCommit fresh)

/-- Successful own cells at the completed original attempt rule out every
failed own raw action, including accepted failures with no public omission. -/
theorem own_joints_not_failed_of_bound (attempt : block.Attempt entry excluded finished after)
    (who : Player) (unique : (Γ.map Prod.fst).Nodup)
    (bound : ∀ {name : VarId} {payload : L.Ty}
      (cell : HasVar Δ name (.commitment who payload)),
      ∃ value, finished.state.get cell = .success value) :
    ∀ joint ∈ attempt.joints, ∀ move, joint who = some move → ¬ move.action.IsFailure := by
  induction attempt with
  | nil => simp only [joints, List.not_mem_nil, false_implies, implies_true]
  | @active Γ Δ O P name owner payload fresh guard rest config excluded finished after
      active choice missed missingFailure later ih =>
      have laterSafe := ih (List.nodup_cons.mpr ⟨fresh, unique⟩) bound
      intro joint member move selected
      rcases List.mem_cons.mp member with rfl | kept
      · by_cases same : who = owner
        · subst who
          simp only [↓reduceIte, Option.some.injEq] at selected
          subst move
          cases choice with
          | success value => simp [OwnAction.IsFailure]
          | failure =>
              have failed := later.preserves_failedBinding owner
                (Config.failedBinding_commit config unique fresh guard O)
              obtain ⟨subject, ty, cell, _, absent⟩ := failed.pending
              obtain ⟨value, present⟩ := bound cell
              rw [absent] at present
              cases present
        · simp only [same, ↓reduceIte] at selected
          cases selected
      · exact laterSafe joint kept move selected
  | @excluded Γ Δ O P name owner payload fresh guard rest config excluded finished after
      inactive later ih =>
      intro joint member move selected
      rcases List.mem_cons.mp member with rfl | kept
      · cases selected
      · exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) bound joint kept move selected

/-- A surviving owner's cells hold values after the attempt exactly when its
original raw word contains no failed action. Guard-rejected domain values are
still values here; this readout does not confuse them with accepted failures. -/
theorem own_bindings_success_iff (attempt : block.Attempt entry excluded finished after)
    (who : Player) (unique : (Γ.map Prod.fst).Nodup)
    (initial : ∀ {name : VarId} {payload : L.Ty}
      (cell : HasVar Γ name (.commitment who payload)),
      ∃ value, entry.state.get cell = .success value)
    (survives : who ∉ after) :
    (∀ {name : VarId} {payload : L.Ty}
      (cell : HasVar Δ name (.commitment who payload)),
      ∃ value, finished.state.get cell = .success value) ↔
    ∀ joint ∈ attempt.joints, ∀ move, joint who = some move → ¬ move.action.IsFailure := by
  refine ⟨attempt.own_joints_not_failed_of_bound who unique, ?_⟩
  intro safe
  induction attempt with
  | nil => exact initial
  | @active Γ Δ O P name owner payload fresh guard rest config excluded finished after
      active choice missed missingFailure later ih =>
      intro finalName finalPayload finalCell
      apply ih (List.nodup_cons.mpr ⟨fresh, unique⟩) _ survives
        (fun joint member => safe joint (List.mem_cons_of_mem _ member)) finalCell
      intro subject ty cell
      cases cell with
      | there cell => exact initial cell
      | here =>
          have head := safe _ (List.mem_cons_self ..)
            ⟨.commit who name payload choice, missed⟩ (by simp only [↓reduceIte])
          cases choice with
          | failure => exact (head rfl).elim
          | success value => exact ⟨value, rfl⟩
  | @excluded Γ Δ O P name owner payload fresh guard rest config excluded finished after
      inactive later ih =>
      intro finalName finalPayload finalCell
      apply ih (List.nodup_cons.mpr ⟨fresh, unique⟩) _ survives
        (fun joint member => safe joint (List.mem_cons_of_mem _ member)) finalCell
      intro subject ty cell
      cases cell with
      | there cell => exact initial cell
      | here => exact (survives (later.excluded_subset inactive)).elim

end Vegas.SourceProgram.CommitPrefix.Attempt
