import Vegas.ViewProjection

/-!
# Visibility Soundness Theorems

Project-facing names for the basic information-flow invariants of Vegas.
The source type system makes public computation consume `erasePubVCtx`, while
the scoping judgment makes commit guards local to the acting player's view.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Payoff evaluation depends only on the public erasure of the terminal
environment. Hidden values can affect payoffs only after they have been
revealed into public state. -/
theorem evalPayoffs_eq_of_erasePubEnv_eq
    {Γ : VCtx P L}
    {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
    {left right : VEnv L Γ}
    (hpub : VEnv.erasePubEnv left = VEnv.erasePubEnv right) :
    evalPayoffs payoffs left = evalPayoffs payoffs right := by
  unfold evalPayoffs
  rw [hpub]

/-- Commit-guard evaluation is invariant under changes outside the committing
player's observation, provided the guard satisfies the Vegas scoping judgment. -/
theorem commitGuard_eval_eq_of_observation_eq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    (hfresh : Fresh x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    {a : L.Val b}
    {left right : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (L := L) (Γ := Γ) who left right) :
    evalGuard (Player := P) (L := L) R a left =
      evalGuard (Player := P) (L := L) R a right :=
  evalGuard_eq_of_obsEq hfresh hR hobs

/-- Equality of projected player views is enough to preserve commit-guard
evaluation. This is the view-kernel form of guard locality. -/
theorem commitGuard_eval_eq_of_projectView_eq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    (hctx : WFCtx (L := L) Γ)
    (hfresh : Fresh x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    {a : L.Val b}
    {left right : Env L.Val (eraseVCtx Γ)}
    (hview : projectViewEnv who left = projectViewEnv who right) :
    evalGuard (Player := P) (L := L) R a left =
      evalGuard (Player := P) (L := L) R a right :=
  evalGuard_eq_of_projectViewEnv_eq hctx hfresh hR hview

end Vegas
