/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitAttempt
import Vegas.Source.CommitRecoveryInstructions

/-! # Actual completed omission masks determine the entire source exclusion scan -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}

/-- The whole chronological exclusion sequence of a decoded completed attempt
reads only its accepted-none mask and inherited exclusions. Source entries and
all hidden accepted values may differ, including accepted failed values. -/
theorem decodeCommitAttempt_exclusionWord_eq
    (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (first second : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (firstEntry secondEntry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (mask : ∀ event, (first.accepted (.inr event)).isNone =
      (second.accepted (.inr event)).isNone) :
    CommitPrefix.Attempt.exclusionsAfter
        (decodeCommitAttempt whole mode block suffix embedding first firstEntry excluded).2.2 =
      CommitPrefix.Attempt.exclusionsAfter
        (decodeCommitAttempt whole mode block suffix embedding second secondEntry excluded).2.2
        := by
  induction block generalizing excluded with
  | nil => rfl
  | @commit Γ Δ O P name owner payload fresh guard rest ih =>
      by_cases inactive : owner ∈ excluded
      · rw [decodeCommitAttempt, dite_eq_left inactive, decodeCommitAttempt, dite_eq_left inactive]
        change excluded :: _ = excluded :: _
        exact congrArg (List.cons excluded) (ih _ _ _ _ _)
      · rw [decodeCommitAttempt, dite_eq_right inactive, decodeCommitAttempt,
          dite_eq_right inactive]
        dsimp only [CommitPrefix.Attempt.exclusionsAfter]
        have same := mask (embedding.event ⟨0, by
          simp only [CommitPrefix.prepend, eventCount]
          omega⟩)
        have head := congrArg (excludeCommit excluded owner) same
        refine congrArg₂ List.cons head ?_
        let afterSecond := commitSuccessor name guard secondEntry
          ((second.accepted (.inr (embedding.event ⟨0, by
            simp only [CommitPrefix.prepend, eventCount]
            omega⟩))).elim PublicationResult.failure fun candidate =>
              second.bindingResult candidate payload)
        have changed := congrArg (fun inherited => CommitPrefix.Attempt.exclusionsAfter
          (decodeCommitAttempt whole mode rest suffix
            (embedding.tail (rest.prepend suffix) (by
              simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl))
            second afterSecond inherited).2.2) head
        exact (ih _ _ _ _ _).trans changed

/-- Equal genuine public completed images have the same full source exclusion
scan, without any equality of their original private inputs or retired words. -/
theorem decodeCommitAttempt_exclusionWord_eq_of_publicView
    (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (first second : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (firstEntry secondEntry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (same : first.publicView = second.publicView) :
    CommitPrefix.Attempt.exclusionsAfter
        (decodeCommitAttempt whole mode block suffix embedding first firstEntry excluded).2.2 =
      CommitPrefix.Attempt.exclusionsAfter
        (decodeCommitAttempt whole mode block suffix embedding second secondEntry excluded).2.2
        := by
  apply decodeCommitAttempt_exclusionWord_eq
  intro event
  exact congrArg (fun view : PublicView ((toEventGraph whole).withMode mode) =>
    (view.accepted (.inr event)).isNone) same

end Vegas
