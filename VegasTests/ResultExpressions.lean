/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ExprSimple

namespace VegasTests.ResultExpressions

open Vegas

private abbrev Empty : CtxSimple := []

example :
    evalExpr (Expr.failure : Expr Empty (.result (.option .bool)))
        (Env.empty Val) = PublicationResult.failure := by
  rfl

example :
    evalExpr (Expr.success Expr.none : Expr Empty (.result (.option .bool)))
        (Env.empty Val) = PublicationResult.success Option.none := by
  rfl

example :
    evalExpr (Expr.success Expr.none : Expr Empty (.result (.option .bool)))
        (Env.empty Val) ≠
      evalExpr (Expr.failure : Expr Empty (.result (.option .bool)))
        (Env.empty Val) := by
  decide

example :
    evalExpr
        (Expr.getResultD (Expr.failure : Expr Empty (.result .int))
          (Expr.constInt 7))
        (Env.empty Val) = 7 := by
  rfl

example :
    evalExpr
        (Expr.getResultD (Expr.success (Expr.constInt 3)) (Expr.constInt 7) :
          Expr Empty .int)
        (Env.empty Val) = 3 := by
  rfl

example :
    evalExpr
        (Expr.isFailure (Expr.failure : Expr Empty (.result .bool)))
        (Env.empty Val) = true := by
  rfl

example :
    exprDeps
        (Expr.getResultD
          (Expr.var 1 (.here) : Expr [(1, .result .int)] (.result .int))
          (Expr.constInt 0)) = {1} := by
  simp [exprDeps]

example :
    IExpr.ResultTypes.valueEquiv (L := simpleExpr) (.option .bool)
        (PublicationResult.success Option.none) =
      PublicationResult.success Option.none := by
  rfl

end VegasTests.ResultExpressions
