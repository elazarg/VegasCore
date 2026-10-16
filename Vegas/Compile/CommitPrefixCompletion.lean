/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitBlockReferences
import Vegas.Compile.EventGraphObservation
import Vegas.Compile.EventGraphPolicy
import Vegas.Source.CommitRecoveryPrefixPath

/-! # Source commitment completions of partially available typed stores -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Read existing binding cells and fill unavailable cells by a latent failed
binding. No physical omission is invented, and no source owner is excluded. -/
def fillCommitPrefix : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : CommitPrefix Γ O Δ P) → (suffix : SourceProgram Player L Δ P) →
    OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (block.prepend suffix) →
    Store (graphLayout whole) → SourceProgram.Config Player L Γ → SourceProgram.Config Player L Δ
  | _, _, _, _, .nil, _, _, _, entry => entry
  | _, _, _, _, .commit name owner fresh guard rest, suffix, embedding, store, entry =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner _) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.ref zero
      let choice := (field.get? store).getD .failure
      let later := embedding.tail (rest.prepend suffix) (by
        simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      fillCommitPrefix rest suffix later store (commitSuccessor name guard entry choice)

/-- The completion is an actual typed attempt, using legal failed values for
unavailable bindings with a false omission bit. -/
def fillCommitPrefix_attempt {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (store : Store (graphLayout whole))
    (entry : SourceProgram.Config Player L Γ) :
    block.Attempt entry ∅ (fillCommitPrefix whole block suffix embedding store entry) ∅ := by
  induction block with
  | nil => exact .nil entry ∅
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.ref zero
      let choice := (field.get? store).getD .failure
      let later := embedding.tail (rest.prepend suffix) (by
        simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      apply CommitPrefix.Attempt.active (Finset.notMem_empty owner) choice false
        (by intro impossible; cases impossible)
      simpa only [fillCommitPrefix, excludeCommit, Bool.false_eq_true, ↓reduceIte] using
        ih suffix later (commitSuccessor name guard entry choice)

/-- Extending a typed commitment observation needs its own visible cell only.
Hidden foreign cells impose no availability requirement. -/
theorem decodeObservation_commit_cons
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (who : Player) (refs : ContextRefs (graphLayout whole) Γ)
    (field : FieldRef (graphLayout whole) (.binding owner payload))
    (store : Store (graphLayout whole)) (state : State L Γ)
    (choice : PublicationResult (L.Val payload))
    (decoded : decodeObservation? who refs store = some (sourceObserve who state))
    (available : owner = who → field.get? store = some choice) :
    decodeObservation? who (refs.cons (name := name) (cell := .commitment owner payload) field)
      store = some (sourceObserve who (Env.cons choice state)) := by
  have observed : sourceObserve who (Env.cons (x := name) choice state) =
      (⟨Env.cons (if owner = who then some choice else none)
        (sourceObserve who state).cells⟩ : SourceObservation L who
          ((name, .commitment owner payload) :: Γ)) := by
    apply congrArg SourceObservation.mk
    funext readName readCell selected
    cases selected with
    | here => rfl
    | there selected => cases readCell <;> rfl
  rw [observed]
  by_cases same : owner = who
  · rw [decodeObservation?, dite_eq_left same]
    change (do
      let value ← field.get? store
      let tail ← decodeObservation? who refs store
      pure (⟨Env.cons (some value) tail.cells⟩ :
        SourceObservation L who ((name, .commitment owner payload) :: Γ))) = _
    rw [available same, decoded]
    simp only [ite_eq_left same]
    rfl
  · rw [decodeObservation?, dite_eq_right same]
    change (do
      let tail ← decodeObservation? who refs store
      pure (⟨Env.cons none tail.cells⟩ :
        SourceObservation L who ((name, .commitment owner payload) :: Γ))) = _
    rw [decoded]
    simp only [ite_eq_right same]
    rfl

/-- A completed visible prefix is preserved by source completion. Missing
foreign hidden bindings may be filled without changing this player's view. -/
theorem fillCommitPrefix_observation {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ) (who : Player)
    (decoded : decodeObservation? who refs store = some (sourceObserve who entry.state))
    (available : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      eventOwner? (block.prepend suffix) index = some who →
        ((embedding.ref index).get? store).isSome = true) :
    decodeObservation? who (commitBlockRefs whole block suffix embedding refs) store =
      some (sourceObserve who
        (fillCommitPrefix whole block suffix embedding store entry).state) := by
  induction block with
  | nil => exact decoded
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.ref zero
      let choice := (field.get? store).getD .failure
      let later := embedding.tail (rest.prepend suffix) (by
        simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have head : owner = who → field.get? store = some choice := by
        intro same
        have present := available zero (by simp only [zero, CommitPrefix.length]; omega)
          (by simpa only [zero, CommitPrefix.prepend, eventOwner?, Fin.mk_zero,
            Fin.cases_zero] using congrArg some same)
        change (field.get? store).isSome = true at present
        cases found : field.get? store with
        | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
        | some value => simp only [choice, found, Option.getD_some]
      have nextDecoded := decodeObservation_commit_cons whole (name := name) who refs field store
        entry.state choice decoded head
      have nextAvailable : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → eventOwner? (rest.prepend suffix) index = some who →
            ((later.ref index).get? store).isSome = true := by
        intro index inside acting
        exact available (Fin.succ index)
          (by simp only [Fin.val_succ, CommitPrefix.length]; omega) acting
      exact ih suffix later (refs.cons (name := name) (cell := .commitment owner payload) field)
        (commitSuccessor name guard entry choice) nextDecoded nextAvailable

end Vegas
