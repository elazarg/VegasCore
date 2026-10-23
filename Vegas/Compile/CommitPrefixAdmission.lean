/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixIntendedCompletion
import Vegas.Source.CommitPrefixIntendedLift

/-! # Guard-admitted source choices in a partially completed commitment phase -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Admitted own values remain admitted when hidden foreign bindings change.
The reference entry must already be intended for this owner; its complete own
view and all owned prefix cells are kept exactly. -/
theorem fillCommitPrefix_intendedFor_congr
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (first second : Store (graphLayout whole))
    (entry reference : SourceProgram.Config Player L Γ) (who : Player)
    (sameEntry : entry.view who = reference.view who)
    (referenceIntended : reference.IntendedFor who O)
    (sameOwned : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → eventOwner? (block.prepend suffix) index = some who →
        (embedding.ref index).get? first = (embedding.ref index).get? second)
    (admitted : (fillCommitPrefix whole block suffix embedding first entry).IntendedFor who P) :
    (fillCommitPrefix whole block suffix embedding second reference).IntendedFor who P := by
  induction block with
  | nil => exact referenceIntended
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.ref zero
      let left := (field.get? first).getD .failure
      let right := (field.get? second).getD .failure
      let later := embedding.tail (rest.prepend suffix) (by
        simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have head : owner = who → left = right := by
        intro own
        have same := sameOwned zero (by simp only [zero, CommitPrefix.length]; omega)
          (by simpa only [zero, CommitPrefix.prepend, eventOwner?, Fin.mk_zero,
            Fin.cases_zero] using congrArg some own)
        change field.get? first = field.get? second at same
        exact congrArg (fun value => value.getD .failure) same
      have oldNext : (commitSuccessor name guard entry left).IntendedFor who (insert name O) :=
        fillCommitPrefix_intendedFor_entry whole rest suffix later first
          (commitSuccessor name guard entry left) who admitted
      have newNext : (commitSuccessor name guard reference right).IntendedFor who
          (insert name O) := by
        by_cases own : owner = who
        · subst owner
          obtain ⟨value, result, accepted⟩ := oldNext.commit_result guard entry left
          have sameResult : right = .success value := (head rfl).symm.trans result
          rw [sameResult]
          apply referenceIntended.commit_own fresh guard value
          exact (congrArg (fun view => guard.predicts view value)
            (congrArg Prod.fst sameEntry)).symm.trans accepted
        · exact referenceIntended.commit_other fresh guard own right
      have nextView := SourceProgram.Config.view_commit_congr name guard entry reference
        sameEntry left right head
      have nextOwned : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → eventOwner? (rest.prepend suffix) index = some who →
            (later.ref index).get? first = (later.ref index).get? second := by
        intro index inside acting
        exact sameOwned (Fin.succ index)
          (by simp only [Fin.val_succ, CommitPrefix.length]; omega) acting
      exact ih suffix later (commitSuccessor name guard entry left)
        (commitSuccessor name guard reference right) nextView newNext nextOwned admitted

/-- Immutable extension preserves the full own admission invariant once its
owned prefix fields were available. Newly filled foreign holes do not matter. -/
theorem fillCommitPrefix_intendedFor_of_extension
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (first second : Store (graphLayout whole))
    (entry : SourceProgram.Config Player L Γ) (who : Player)
    (preserved : ∀ field value, first field = some value → second field = some value)
    (available : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → eventOwner? (block.prepend suffix) index = some who →
        ((embedding.ref index).get? first).isSome = true)
    (admitted : (fillCommitPrefix whole block suffix embedding first entry).IntendedFor who P) :
    (fillCommitPrefix whole block suffix embedding second entry).IntendedFor who P := by
  apply fillCommitPrefix_intendedFor_congr whole block suffix embedding first second entry entry
    who rfl (fillCommitPrefix_intendedFor_entry whole block suffix embedding first entry who
      admitted) _ admitted
  intro index inside owned
  have present := available index inside owned
  cases found : (embedding.ref index).get? first with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
  | some value =>
      exact ((embedding.ref index).get?_preserved first second preserved value found).symm

/-- When every owner's actual prefix is admitted, the actual filled phase is
intended as a whole. The saved continuation guard condition is propagated at
each successful commitment, so future satisfiability is retained too. -/
theorem fillCommitPrefix_intended {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (store : Store (graphLayout whole))
    (entry : SourceProgram.Config Player L Γ)
    (intended : ProtocolState.Intended (block.prepend suffix)
      (ProtocolState.entry (block.prepend suffix) entry))
    (admitted : ∀ who, (fillCommitPrefix whole block suffix embedding store entry).IntendedFor
      who P) :
    ProtocolState.Intended suffix (ProtocolState.entry suffix
      (fillCommitPrefix whole block suffix embedding store entry)) := by
  induction block with
  | nil => exact intended
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
          suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          embedding.ref zero
      let result := (field.get? store).getD .failure
      let later := embedding.tail (rest.prepend suffix) (by
        simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have nextAdmitted (who : Player) :
          (fillCommitPrefix whole rest suffix later store
            (commitSuccessor name guard entry result)).IntendedFor who P := admitted who
      have head := fillCommitPrefix_intendedFor_entry whole rest suffix later store
        (commitSuccessor name guard entry result) owner (nextAdmitted owner)
      obtain ⟨value, equal, accepted⟩ := head.commit_result guard entry result
      change entry.Intended O ∧ GuardsSatisfiableFrom
        (.commit name owner fresh guard (rest.prepend suffix)) entry at intended
      have nextIntended := ProtocolState.intended_entry (rest.prepend suffix)
        (commitSuccessor name guard entry (.success value))
        (intended.1.commit fresh guard value accepted) (intended.2.2 value accepted)
      rw [← equal] at nextIntended
      exact ih suffix later (commitSuccessor name guard entry result) nextIntended nextAdmitted

end Vegas
