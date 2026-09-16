/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Foundation.ExprInterface

/-! # Finite expression domains

Opt-in finite-domain evidence for expression values. This interface
is independent of program syntax; an unbounded payoff type need not provide it.
-/

namespace Vegas

/-- A finite semantic domain for one expression-language type. Concrete
languages can provide instances for bounded types, while leaving unbounded
types such as payoff integers without an instance. -/
class FiniteType (L : IExpr) (τ : L.Ty) where
  fintype : Fintype (L.Val τ)

noncomputable instance instFintypeOfFiniteType
    (L : IExpr) (τ : L.Ty) [h : FiniteType L τ] :
    Fintype (L.Val τ) :=
  h.fintype

end Vegas
