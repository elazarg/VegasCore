/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixAtEvent
import Vegas.Source.CommitPrefixWord

/-! # Concrete typed splits of the same compiled commitment block -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- The actual binding layout selects the instruction and its typed owner
inside the SAME original commitment block, retaining its complete suffix. -/
theorem binding_split_of_layout (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) :
    ∀ (selected : Fin (eventCount (block.prepend suffix))), selected.val < block.length →
      ∀ (who : Player) (payload : L.Ty),
      outputLayout (block.prepend suffix) selected = .binding who payload →
        ∃ (Ξ : SourceCtx Player L) (Q : Finset VarId) (name : VarId)
          (fresh : name ∉ Ξ.map Prod.fst) (guard : SourceGuard L Ξ who name payload)
          (earlier : CommitPrefix Γ O Ξ Q)
          (later : CommitPrefix ((name, .commitment who payload) :: Ξ) (insert name Q) Δ P),
          earlier.length = selected.val ∧
            earlier.append (.commit name who fresh guard later) = block := by
  induction block with
  | nil => intro selected inside; simp only [length] at inside; omega
  | @commit Γ O Δ P name owner value fresh guard rest ih =>
      intro selected
      refine Fin.cases ?_ ?_ selected
      · intro _inside who payload layout
        change EventField.binding owner value = EventField.binding who payload at layout
        cases layout
        exact ⟨_, _, name, fresh, guard, .nil, rest, rfl, rfl⟩
      · intro later inside who payload layout
        obtain ⟨Ξ, Q, nextName, nextFresh, nextGuard, earlier, after, size, reconstruct⟩ :=
          ih suffix later (by change later.val + 1 < rest.length + 1 at inside; omega)
            who payload layout
        refine ⟨Ξ, Q, nextName, nextFresh, nextGuard,
          .commit name owner fresh guard earlier, after, ?_, ?_⟩
        · exact congrArg Nat.succ size
        · exact congrArg (CommitPrefix.commit name owner fresh guard) reconstruct

end Vegas.SourceProgram.CommitPrefix
