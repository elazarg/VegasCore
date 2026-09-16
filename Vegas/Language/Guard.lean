/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Language.Env

/-! # Guard evaluation for the surface-language prototype

The surface feasibility predicate evaluates guards against a proposed value
and a player-visible environment. This evaluator does not define when a
compiled protocol validates a commitment.
-/

namespace Vegas

/-- Evaluate a surface guard in the extended visible context. -/
def evalGuard {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} {b : L.Ty} {x : VarId}
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
    (a : L.Val b) (env : Env L.Val (eraseVCtx Γ)) : Bool :=
  L.toBool (L.eval R (Env.cons a env))

end Vegas
