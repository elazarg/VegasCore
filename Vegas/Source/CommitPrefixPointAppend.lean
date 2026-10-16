/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixWord
import Vegas.Source.CommitRecoveryBlockEmbedding

/-! # Exact source points under commitment prefix concatenation -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem commit_state_cast_inr {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    {first second : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name O)} (same : first = second) (point : ProtocolState first) :
    cast (congrArg ProtocolState (congrArg (SourceProgram.commit name owner fresh guard) same))
        (Sum.inr point) =
      Sum.inr (cast (congrArg ProtocolState same) point) := by
  cases same
  rfl

/-- Reassociating typed commitment prefixes retains the exact original
source point, including its store, registry and full private action records. -/
theorem liftPoint_append {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q) (point : ProtocolState suffix) :
    cast (congrArg ProtocolState (earlier.prepend_append later suffix))
        ((earlier.append later).liftPoint suffix point) =
      earlier.liftPoint (later.prepend suffix) (later.liftPoint suffix point) := by
  induction earlier with
  | nil => rfl
  | commit name owner fresh guard rest ih =>
      change cast (congrArg ProtocolState
          (congrArg (SourceProgram.commit name owner fresh guard)
            (rest.prepend_append later suffix)))
          (Sum.inr ((rest.append later).liftPoint suffix point)) =
        Sum.inr (rest.liftPoint (later.prepend suffix) (later.liftPoint suffix point))
      rw [commit_state_cast_inr fresh guard (rest.prepend_append later suffix)]
      exact congrArg Sum.inr (ih later)

end Vegas.SourceProgram.CommitPrefix
