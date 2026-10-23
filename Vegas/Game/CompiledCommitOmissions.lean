/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledCommitAttempt

/-! # Physical omission sets of decoded commitment attempts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

/-- Owners with an absent accepted receipt in the exact compiled source block.
This set does not inspect hidden candidate values. -/
def commitMissingOwners : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : SourceProgram.CommitPrefix Γ O Δ P) →
    (suffix : SourceProgram Player L Δ P) →
    OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (block.prepend suffix) →
    EventGraphRuntime.State ((toEventGraph whole).withMode mode) → Finset Player
  | _, _, _, _, .nil, _suffix, _embedding, _native => ∅
  | _, _, _, _, .commit _ owner _ _ rest, suffix, embedding, native =>
      let event := embedding.event ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let laterEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let later := commitMissingOwners rest suffix laterEmbedding native
      if native.accepted (.inr event) = none then insert owner later else later

/-- The decoder's omission set is read from the actual compiled event addresses. -/
theorem mem_commitMissingOwners {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode)) (who : Player) :
    who ∈ commitMissingOwners whole mode block suffix embedding native ↔
      ∃ index : Fin (eventCount (block.prepend suffix)), index.val < block.length ∧
        ((toEventGraph whole).withMode mode).actor? (embedding.event index) = some who ∧
        native.accepted (.inr (embedding.event index)) = none := by
  induction block with
  | nil => simp only [commitMissingOwners, SourceProgram.CommitPrefix.length,
      Finset.notMem_empty, Nat.not_lt_zero, false_and, exists_false]
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let laterEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have headActor : ((toEventGraph whole).withMode mode).actor? (embedding.event zero) =
          some owner := EventGraph.actor?_of_outputLayout_binding _ (embedding.layout_eq zero)
      have membership : who ∈ commitMissingOwners whole mode
          (.commit name owner fresh guard rest) suffix embedding native ↔
          (who = owner ∧ native.accepted (.inr (embedding.event zero)) = none) ∨
            who ∈ commitMissingOwners whole mode rest suffix laterEmbedding native := by
        change who ∈ (if native.accepted (.inr (embedding.event zero)) = none then
          insert owner (commitMissingOwners whole mode rest suffix laterEmbedding native)
          else commitMissingOwners whole mode rest suffix laterEmbedding native) ↔ _
        by_cases omitted : native.accepted (.inr (embedding.event zero)) = none <;>
          simp only [omitted, ↓reduceIte, Finset.mem_insert, and_true, and_false, false_or]
      rw [membership, ih suffix laterEmbedding]
      constructor
      · rintro (⟨same, omitted⟩ | ⟨index, inside, acting, omitted⟩)
        · subst who
          exact ⟨zero, by simp only [zero, SourceProgram.CommitPrefix.length]; omega,
            headActor, omitted⟩
        · exact ⟨Fin.succ index, by
            change index.val + 1 < rest.length + 1
            omega, acting, omitted⟩
      · rintro ⟨index, inside, acting, omitted⟩
        revert inside acting omitted
        refine Fin.cases ?_ ?_ index
        · intro _inside acting omitted
          left
          exact ⟨(Option.some.inj (headActor.symm.trans acting)).symm, omitted⟩
        · intro later inside acting omitted
          right
          exact ⟨later, by
            change later.val + 1 < rest.length + 1 at inside
            omega, acting, omitted⟩

end Vegas
