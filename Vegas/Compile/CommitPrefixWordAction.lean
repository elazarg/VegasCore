/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixWord
import Vegas.Compile.EventGraphBacktranslation

/-! # Genuine compiled actions read from an owned commitment word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At every owned static position in a commitment telescope, the word reader
returns a genuine action of that exact compiled event, including failure.
No support, profile or availability premise is required. -/
theorem compiledCommitPrefix_wordAction_decodable
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} (block : CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P) (who : Player)
      (event : Fin (eventCount (block.prepend suffix))),
      event.val < block.length → eventOwner? (block.prepend suffix) event = some who →
      ∀ word : DecisionView who Δ,
        ∃ (action : OwnAction Player L)
          (native : EventField.Action (outputLayout (block.prepend suffix) event)),
          block.wordAction who event.val word = some action ∧
            decodeEventAction (block.prepend suffix) event native = some action := by
  induction block with
  | nil =>
    intro suffix who event impossible
    simp only [CommitPrefix.length] at impossible
    omega
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
    intro suffix who event
    refine Fin.cases ?_ ?_ event
    · intro _inside owned word
      change some owner = some who at owned
      have same : owner = who := Option.some.inj owned
      subst who
      let result : PublicationResult (L.Val payload) :=
        (((rest.entryView owner word).1.cells name (.commitment owner payload) .here).getD .failure)
      refine ⟨.commit owner name payload result, result, ?_, ?_⟩
      · simp only [CommitPrefix.wordAction, ite_true]
        rfl
      · rfl
    · intro tail inside owned word
      obtain ⟨action, native, read, decoded⟩ := ih suffix who tail
        (by simpa only [CommitPrefix.length, Fin.val_succ, Nat.succ_lt_succ_iff] using inside)
        owned word
      exact ⟨action, native, read, decoded⟩

end Vegas
