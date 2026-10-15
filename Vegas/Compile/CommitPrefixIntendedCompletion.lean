/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixCompletion
import Vegas.Source.IntendedCommitPredecessor
import Vegas.Source.CommitBlockInformation

/-! # Intended completion of hidden foreign commitment cells -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Own admissibility at the end of a filled typed prefix reflects to its entry,
regardless of the failed hidden foreign values used in that reference fill. -/
theorem fillCommitPrefix_intendedFor_entry {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (store : Store (graphLayout whole))
    (entry : SourceProgram.Config Player L Γ) (who : Player)
    (after : (fillCommitPrefix whole block suffix embedding store entry).IntendedFor who P) :
    entry.IntendedFor who O := by
  induction block with
  | nil => exact after
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      have head := ih suffix _ _ after
      exact SourceProgram.Config.IntendedFor.commit_before fresh guard entry _ head

/-- Hidden foreign values are filled by genuine guard-admitted source values.
Owned reference values are retained using their reflected own admissibility;
all subsequent choices use the updated source observations and own history. -/
theorem fillCommitPrefix_intended_completion {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (store : Store (graphLayout whole))
    (reference entry : SourceProgram.Config Player L Γ) (who : Player)
    (intended : ProtocolState.Intended (block.prepend suffix)
      (ProtocolState.entry (block.prepend suffix) entry))
    (sameView : entry.view who = reference.view who)
    (ownAdmitted : (fillCommitPrefix whole block suffix embedding store reference).IntendedFor
      who P) :
    ∃ final : SourceProgram.Config Player L Δ,
      Nonempty (block.Attempt entry ∅ final ∅) ∧
      ProtocolState.Intended suffix (ProtocolState.entry suffix final) ∧
      final.view who =
        (fillCommitPrefix whole block suffix embedding store reference).view who := by
  induction block with
  | nil => exact ⟨entry, ⟨.nil entry ∅⟩, intended, sameView⟩
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using embedding.ref zero
      let result := (field.get? store).getD .failure
      let later := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let referenceNext := commitSuccessor name guard reference result
      have ownNext : referenceNext.IntendedFor who (insert name O) :=
        fillCommitPrefix_intendedFor_entry whole rest suffix later store referenceNext who
          ownAdmitted
      change entry.Intended O ∧ GuardsSatisfiableFrom
        (.commit name owner fresh guard (rest.prepend suffix)) entry at intended
      have chosen : ∃ value, guard.predicts (sourceObserve owner entry.state) value = true ∧
          (owner = who → result = .success value) := by
        by_cases own : owner = who
        · subst owner
          obtain ⟨value, equal, accepted⟩ := ownNext.commit_result guard reference result
          refine ⟨value, ?_, fun _ => equal⟩
          exact (congrArg (fun view => guard.predicts view value)
            (congrArg Prod.fst sameView)).trans accepted
        · obtain ⟨value, accepted⟩ := intended.2.1
          exact ⟨value, accepted, fun impossible => (own impossible).elim⟩
      obtain ⟨value, accepted, sameResult⟩ := chosen
      have nextIntended := ProtocolState.intended_entry (rest.prepend suffix)
        (commitSuccessor name guard entry (.success value))
        (intended.1.commit fresh guard value accepted) (intended.2.2 value accepted)
      have nextView := SourceProgram.Config.view_commit_congr name guard entry reference sameView
        (.success value) result (fun own => (sameResult own).symm)
      obtain ⟨final, ⟨attempt⟩, finalIntended, finalView⟩ := ih suffix later referenceNext
        (commitSuccessor name guard entry (.success value)) nextIntended nextView ownAdmitted
      exact ⟨final, ⟨.active (Finset.notMem_empty owner) (.success value) false
        (by intro impossible; cases impossible) attempt⟩, finalIntended, finalView⟩

end Vegas
