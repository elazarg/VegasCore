/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixSplitting

/-! # Final-instruction decomposition of typed commitment telescopes -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} {L : IExpr}

/-- Append one actual typed commitment to the end of a commitment telescope. -/
def snoc {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload) :
    CommitPrefix Γ O ((name, .commitment owner payload) :: Δ) (insert name P) :=
  match block with
  | .nil => .commit name owner fresh guard .nil
  | .commit prior author priorFresh priorGuard rest =>
      .commit prior author priorFresh priorGuard (rest.snoc name owner fresh guard)

/-- Appending an instruction adds one commitment slot. -/
theorem length_snoc {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload) :
    (block.snoc name owner fresh guard).length = block.length + 1 := by
  induction block with
  | nil => rfl
  | commit _ _ _ _ _ ih => simp only [snoc, length, ih]

/-- The final instruction is the first instruction of the original suffix. -/
theorem prepend_snoc [DecidableEq Player] [IExpr.ResultTypes L]
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P)) :
    (block.snoc name owner fresh guard).prepend next =
      block.prepend (.commit name owner fresh guard next) := by
  induction block with
  | nil => rfl
  | commit prior author priorFresh priorGuard _rest ih =>
      exact congrArg (SourceProgram.commit prior author priorFresh priorGuard) (ih fresh guard next)

/-- Every nonempty telescope has an actual typed final commitment. The
heterogeneous equality retains its exact ending context and obligation set. -/
theorem exists_snoc {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (positive : 0 < block.length) :
    ∃ (Ξ : SourceCtx Player L) (Q : Finset VarId) (name : VarId) (owner : Player)
      (payload : L.Ty) (fresh : name ∉ Ξ.map Prod.fst)
      (guard : SourceGuard L Ξ owner name payload) (earlier : CommitPrefix Γ O Ξ Q),
      Δ = (name, .commitment owner payload) :: Ξ ∧ P = insert name Q ∧
        HEq block (earlier.snoc name owner fresh guard) := by
  induction block with
  | nil => simp only [length] at positive; omega
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      cases rest with
      | nil => exact ⟨Γ, O, name, owner, payload, fresh, guard, .nil, rfl, rfl, HEq.rfl⟩
      | commit nextName nextOwner nextFresh nextGuard later =>
          obtain ⟨Ξ, Q, finalName, finalOwner, finalPayload, finalFresh, finalGuard, earlier,
            contextEq, pendingEq, equal⟩ := ih (by simp only [length]; omega)
          cases contextEq
          cases pendingEq
          refine ⟨Ξ, Q, finalName, finalOwner, finalPayload, finalFresh, finalGuard,
            .commit name owner fresh guard earlier, rfl, rfl, ?_⟩
          exact heq_of_eq (congrArg (CommitPrefix.commit name owner fresh guard)
            (eq_of_heq equal))

end Vegas.SourceProgram.CommitPrefix
