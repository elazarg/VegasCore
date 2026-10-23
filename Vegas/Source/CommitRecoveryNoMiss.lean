/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryObservedClosure

/-! # Replaying a source commitment prefix without new omissions

The replay retains the original exclusion set and every originally active
typed choice. A newly excluded owner's later automatic bindings become
accepted failed bindings. Every surviving owner's complete observation is
preserved, including its original private inputs and chronological own word.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Config

/-- A foreign automatic binding and an accepted failed binding have the same
complete observer view; only the binding owner's action word can differ. -/
theorem automaticCommit_view_eq_failure {Γ : SourceCtx Player L} {payload : L.Ty}
    (who owner : Player) (different : owner ≠ who) (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : Config Player L Γ) :
    (automaticCommit name owner payload config).view who =
      (commitSuccessor name guard config .failure).view who := by
  apply Prod.ext
  · rfl
  · change config.history who =
      (Function.update config.history owner
        (config.history owner ++ [OwnAction.commit owner name payload .failure])) who
    rw [Function.update_of_ne (Ne.symm different)]

end Config

namespace CommitPrefix.Attempt

/-- Replay the actual typed choices, using the saved exclusion set throughout.
The replacement entry permits the same operation after an earlier private
history has been erased. No new setup value or binding is sampled. -/
def withoutMisses : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    {block : CommitPrefix Γ O Δ P} → {entry : Config Player L Γ} →
    {excluded : Finset Player} → {finished : Config Player L Δ} →
    {after : Finset Player} → block.Attempt entry excluded finished after →
      Finset Player → Config Player L Γ → Config Player L Δ
  | _, _, _, _, _, _, _, _, _, .nil _ _, _, replacement => replacement
  | _, _, _, _, _, _, _, _, _,
      .active (name := name) (guard := guard) _ choice _ _ later, saved, replacement =>
      later.withoutMisses saved (commitSuccessor name guard replacement choice)
  | _, _, _, _, _, _, _, _, _,
      .excluded (name := name) (owner := owner) (payload := payload) (guard := guard) _ later,
      saved, replacement =>
      if owner ∈ saved then
        later.withoutMisses saved (automaticCommit name owner payload replacement)
      else later.withoutMisses saved (commitSuccessor name guard replacement .failure)

/-- The replay is a genuine attempt with exactly the saved exclusions. In
particular an accepted failed binding is not turned into an omission. -/
def withoutMisses_attempt
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after)
    (saved : Finset Player) (inherited : saved ⊆ excluded) (replacement : Config Player L Γ) :
    block.Attempt replacement saved (attempt.withoutMisses saved replacement) saved := by
  induction attempt with
  | nil config excluded => exact .nil replacement saved
  | @active Γ Δ O P name owner payload fresh guard rest config excluded final after
      active choice missed missingFailure later ih =>
      refine .active (fun member => active (inherited member)) choice false
        (fun impossible => Bool.noConfusion impossible) ?_
      apply ih _ (commitSuccessor name guard replacement choice)
      intro who member
      cases missed with
      | false => exact inherited member
      | true => exact Finset.mem_insert_of_mem (inherited member)
  | @excluded Γ Δ O P name owner payload fresh guard rest config excluded final after
      inactive later ih =>
      by_cases kept : owner ∈ saved
      · simpa only [withoutMisses, kept, ↓reduceIte] using
          (CommitPrefix.Attempt.excluded kept
            (ih inherited (automaticCommit name owner payload replacement)))
      · simpa only [withoutMisses, kept, ↓reduceIte] using
          (CommitPrefix.Attempt.active kept .failure false
            (fun impossible => Bool.noConfusion impossible)
            (ih inherited (commitSuccessor name guard replacement .failure)))

/-- New foreign omissions and their automatic suffix steps do not change any
surviving owner's source query. Its entire private tuple and own word are
retained, rather than independently resampled or postulated equal. -/
theorem withoutMisses_surviving_view
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after)
    (saved : Finset Player) (replacement : Config Player L Γ) (who : Player)
    (sameEntry : entry.view who = replacement.view who) (survives : who ∉ after) :
    finished.view who = (attempt.withoutMisses saved replacement).view who := by
  induction attempt with
  | nil config excluded => exact sameEntry
  | @active Γ Δ O P name owner payload fresh guard rest config excluded final after
      active choice missed missingFailure later ih =>
      exact ih (commitSuccessor name guard replacement choice)
        (Config.view_commit_congr name guard config replacement sameEntry choice choice
          (fun _ => rfl)) survives
  | @excluded Γ Δ O P name owner payload fresh guard rest config excluded final after
      inactive later ih =>
      have different : owner ≠ who := fun same =>
        survives (same ▸ later.excluded_subset inactive)
      by_cases kept : owner ∈ saved
      · simp only [withoutMisses, kept, ↓reduceIte]
        exact ih (automaticCommit name owner payload replacement)
          (Config.view_automaticCommit_congr who owner name payload config replacement sameEntry)
          survives
      · simp only [withoutMisses, kept, ↓reduceIte]
        apply ih (commitSuccessor name guard replacement .failure) _ survives
        exact (Config.view_automaticCommit_congr who owner name payload config replacement
          sameEntry).trans
            (Config.automaticCommit_view_eq_failure who owner different name guard replacement)

end CommitPrefix.Attempt
end Vegas.SourceProgram
