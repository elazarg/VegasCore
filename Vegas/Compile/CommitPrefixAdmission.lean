/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixIntendedCompletion

/-! # Guard-admitted source choices in a partially completed commitment phase -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

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
