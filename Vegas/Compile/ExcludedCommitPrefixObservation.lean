/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.CommitPrefixCompletion

/-! # Latent commitment-prefix completions with permanent source exclusions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Filling the same cells preserves an earlier own-word prefix difference,
independently of the initial hidden state and guard bookkeeping. -/
theorem fillCommitPrefix_history_prefix
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (store : Store (graphLayout whole))
    (first second : SourceProgram.Config Player L Γ) (who : Player)
    (earlierWord : List (OwnAction Player L))
    (same : first.history who = earlierWord ++ second.history who) :
    (fillCommitPrefix whole block suffix embedding store first).history who =
      earlierWord ++ (fillCommitPrefix whole block suffix embedding store second).history who := by
  induction block with
  | nil => exact same
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      dsimp only [fillCommitPrefix]
      apply ih
      change Function.update first.history owner
          (first.history owner ++ [OwnAction.commit owner name payload _]) who =
        earlierWord ++ Function.update second.history owner
          (second.history owner ++ [OwnAction.commit owner name payload _]) who
      by_cases equal : who = owner
      · subst who
        simp only [Function.update_self, same, List.append_assoc]
      · simpa only [Function.update_of_ne equal] using same

/-- Complete a partial commitment prefix as a genuine source attempt without
inventing new exclusions. Already excluded owners execute automatically;
unavailable hidden active bindings use an accepted failed value. The entire
visible typed observation of a surviving owner is unchanged. -/
theorem exists_commitPrefix_attempt_observation
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (excluded : Finset Player) (who : Player) (survives : who ∉ excluded)
    (decoded : decodeObservation? who refs store = some (sourceObserve who entry.state))
    (available : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      eventOwner? (block.prepend suffix) index = some who →
        ((embedding.ref index).get? store).isSome = true) :
    ∃ finished : SourceProgram.Config Player L Δ,
      Nonempty (block.Attempt entry excluded finished excluded) ∧
      decodeObservation? who (commitBlockRefs whole block suffix embedding refs) store =
        some (sourceObserve who finished.state) ∧
      finished.history who = (fillCommitPrefix whole block suffix embedding store entry).history who
        := by
  induction block with
  | nil => exact ⟨entry, ⟨.nil entry excluded⟩, decoded, rfl⟩
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.ref zero
      let later := embedding.tail (rest.prepend suffix) (by
        simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have nextAvailable : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → eventOwner? (rest.prepend suffix) index = some who →
            ((later.ref index).get? store).isSome = true := by
        intro index inside acting
        exact available (Fin.succ index)
          (by simp only [Fin.val_succ, CommitPrefix.length]; omega) acting
      by_cases inactive : owner ∈ excluded
      · have different : owner ≠ who := fun same => survives (same ▸ inactive)
        have nextDecoded := decodeObservation_commit_cons whole (name := name) who refs field
          store entry.state .failure decoded (fun same => (different same).elim)
        obtain ⟨finished, ⟨attempt⟩, observation, word⟩ := ih suffix later
          (refs.cons (name := name) (cell := .commitment owner payload) field)
          (automaticCommit name owner payload entry) nextDecoded nextAvailable
        refine ⟨finished, ⟨.excluded inactive attempt⟩, observation, ?_⟩
        apply word.trans
        simpa only [List.nil_append, fillCommitPrefix, zero, field, later] using
          fillCommitPrefix_history_prefix whole rest suffix later
          store (automaticCommit name owner payload entry)
          (commitSuccessor name guard entry ((field.get? store).getD .failure)) who [] (by
            simp only [automaticCommit, commitSuccessor, Function.update_of_ne different.symm,
              List.nil_append])
      · let choice := (field.get? store).getD .failure
        have head : owner = who → field.get? store = some choice := by
          intro same
          have present := available zero (by simp only [zero, CommitPrefix.length]; omega)
            (by simpa only [zero, CommitPrefix.prepend, eventOwner?, Fin.mk_zero,
              Fin.cases_zero] using congrArg some same)
          change (field.get? store).isSome = true at present
          cases found : field.get? store with
          | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
          | some value => simp only [choice, found, Option.getD_some]
        have nextDecoded := decodeObservation_commit_cons whole (name := name) who refs field
          store entry.state choice decoded head
        obtain ⟨finished, ⟨attempt⟩, observation, word⟩ := ih suffix later
          (refs.cons (name := name) (cell := .commitment owner payload) field)
          (commitSuccessor name guard entry choice) nextDecoded nextAvailable
        exact ⟨finished, ⟨.active inactive choice false (by intro impossible; cases impossible)
          attempt⟩, observation, word⟩

end Vegas
