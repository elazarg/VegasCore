/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.CommitPrefixCompletion
import Vegas.Source.CommitBlockInformation

/-! # Immutable owner observations in a partially completed commitment prefix -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Equal owned binding cells give the same complete source view. Hidden foreign
cells may differ, including unavailable cells filled by latent failures. -/
theorem fillCommitPrefix_view_congr {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (first second : Store (graphLayout whole))
    (entry reference : SourceProgram.Config Player L Γ) (who : Player)
    (sameEntry : entry.view who = reference.view who)
    (sameOwned : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → eventOwner? (block.prepend suffix) index = some who →
        (embedding.ref index).get? first = (embedding.ref index).get? second) :
    (fillCommitPrefix whole block suffix embedding first entry).view who =
      (fillCommitPrefix whole block suffix embedding second reference).view who := by
  induction block with
  | nil => exact sameEntry
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.ref zero
      let later := embedding.tail (rest.prepend suffix) (by
        simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have head : owner = who → (field.get? first).getD .failure =
          (field.get? second).getD .failure := by
        intro own
        have same := sameOwned zero (by simp only [zero, CommitPrefix.length]; omega)
          (by simpa only [zero, CommitPrefix.prepend, eventOwner?, Fin.mk_zero,
            Fin.cases_zero] using congrArg some own)
        change field.get? first = field.get? second at same
        rw [same]
      have nextView := SourceProgram.Config.view_commit_congr name guard entry reference
        sameEntry _ _ head
      have nextOwned : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → eventOwner? (rest.prepend suffix) index = some who →
            (later.ref index).get? first = (later.ref index).get? second := by
        intro index inside acting
        exact sameOwned (Fin.succ index)
          (by simp only [Fin.val_succ, CommitPrefix.length]; omega) acting
      exact ih suffix later
        (commitSuccessor name guard entry ((field.get? first).getD .failure))
        (commitSuccessor name guard reference ((field.get? second).getD .failure))
        nextView nextOwned

/-- Once every earlier owned binding is present, an immutable store extension
cannot alter the author's predecessor observation or its full source own word. -/
theorem fillCommitPrefix_view_of_extension {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (first second : Store (graphLayout whole))
    (entry : SourceProgram.Config Player L Γ) (who : Player)
    (preserved : ∀ field value, first field = some value → second field = some value)
    (available : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → eventOwner? (block.prepend suffix) index = some who →
        ((embedding.ref index).get? first).isSome = true) :
    (fillCommitPrefix whole block suffix embedding first entry).view who =
      (fillCommitPrefix whole block suffix embedding second entry).view who := by
  apply fillCommitPrefix_view_congr whole block suffix embedding first second entry entry who rfl
  intro index inside owned
  have present := available index inside owned
  cases found : (embedding.ref index).get? first with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
  | some value =>
      exact ((embedding.ref index).get?_preserved first second preserved value found).symm

end Vegas
