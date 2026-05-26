/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Lang.Basic

/-!
# Nullable guard facts

Surface `yield` lowering uses nullable hidden commitments. This file records
the guard facts for those synthesized nullable commitments.
-/

namespace Vegas

variable {P : Type} [DecidableEq P]

namespace VegasLang

/-- The nullable action synthesized by compilation is always guard-legal:
choosing `none` satisfies the compiled guard independently of the source guard.
-/
theorem nullableGuard_none_legal
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (env : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := simpleExpr)
      (Expr.nullableCommitGuard R) Option.none env = true := by
  change evalExpr (Expr.nullableCommitGuard R)
      (Env.cons (x := secret) Option.none env) = true
  exact evalExpr_nullableCommitGuard_none R env

/-- On ordinary source values, the compiled nullable guard agrees with the
original guard. -/
theorem nullableGuard_some_eq
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (v : Val b) (env : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := simpleExpr)
        (Expr.nullableCommitGuard R) (some v) env =
      evalGuard (Player := P) (L := simpleExpr) R v env := by
  change evalExpr (Expr.nullableCommitGuard R)
      (Env.cons (x := secret) (some v) env) =
    evalExpr R (Env.cons (x := secret) v env)
  exact evalExpr_nullableCommitGuard_some R v env

/-- Every compiled nullable guard has at least one legal action in every
environment, namely `none`. -/
theorem nullableGuard_satisfiable
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool) :
    ∀ env : Env Val (eraseVCtx Γ),
      ∃ a : Val (.option b),
        evalGuard (Player := P) (L := simpleExpr)
          (Expr.nullableCommitGuard R) a env = true := by
  exact nullableCommitGuard_satisfiable R

end VegasLang

end Vegas
