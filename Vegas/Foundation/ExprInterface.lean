/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.Context
import Vegas.Foundation.Probability

/-!
# The embedded expression-language interface `IExpr`

`IExpr` packages the concrete expression layer: types, values, expression and
distribution syntax, evaluation, dependency tracking, and the soundness laws
that justify treating `exprDeps` as a static over-approximation of semantic
dependence. Everything else in Vegas is generic over this interface.
-/

namespace Vegas

open GameTheory.Math.Probability

/-! ## The expression-language interface `IExpr` -/

/-- Core PL interface for the Vegas layer.

Packages the concrete expression layer: types, values, expression syntax,
distribution syntax, evaluation functions, dependency tracking, and
dependency-soundness laws. Expressions and distributions are typed over plain
`Ctx Ty` (no visibility annotations) — visibility is layered separately by the
`VCtx` family below. -/
structure IExpr where
  /-- The universe of types in the embedded language. -/
  Ty : Type
  /-- Semantic interpretation: the values inhabiting each type. -/
  Val : Ty → Type
  decEqTy : DecidableEq Ty
  decEqVal : ∀ {τ : Ty}, DecidableEq (Val τ)
  /-- A distinguished Boolean-representing type. Used for commit guards. -/
  bool : Ty
  /-- Project a value of `bool` into Lean's `Bool`. -/
  toBool : Val bool → Bool
  /-- A distinguished integer-representing type. Used for per-player payoffs. -/
  int : Ty
  /-- Project a value of `int` into Lean's `Int`. -/
  toInt : Val int → Int
  /-- Typed expression syntax. -/
  Expr : Ctx Ty → Ty → Type
  /-- Denotational evaluation. -/
  eval : {Γ : Ctx Ty} → {τ : Ty} → Expr Γ τ → Env Val Γ → Val τ
  /-- A static over-approximation of the variables an expression reads.
  Sound by `expr_deps_sound`. -/
  exprDeps : {Γ : Ctx Ty} → {τ : Ty} → Expr Γ τ → Finset VarId
  /-- Evaluate an expression from values for only its declared dependencies. -/
  evalDeps :
    {Γ : Ctx Ty} → {τ : Ty} → (e : Expr Γ τ) →
      ((x : VarId) → (σ : Ty) → HasVar Γ x σ → x ∈ exprDeps e → Val σ) →
        Val τ
  /-- Dependency sets mention only variables available in the expression
  context. This is the structural companion to semantic dependency soundness. -/
  expr_deps_context :
    ∀ {Γ : Ctx Ty} {τ : Ty} (e : Expr Γ τ),
      ∀ x, x ∈ exprDeps e → x ∈ Γ.map Prod.fst
  /-- Typed distribution syntax. -/
  DistExpr : Ctx Ty → Ty → Type
  /-- Evaluate distribution syntax to an exact, normalized rational table.
  This table is retained for execution lowering; semantic game laws are
  derived from it with `RationalLaw.denote`. -/
  evalLaw : {Γ : Ctx Ty} → {τ : Ty} →
    DistExpr Γ τ → Env Val Γ → RationalLaw (Val τ)
  /-- Static over-approximation of variables a distribution reads. -/
  distDeps : {Γ : Ctx Ty} → {τ : Ty} → DistExpr Γ τ → Finset VarId
  /-- Distribution dependency sets mention only variables available in the
  distribution context. -/
  dist_deps_context :
    ∀ {Γ : Ctx Ty} {τ : Ty} (d : DistExpr Γ τ),
      ∀ x, x ∈ distDeps d → x ∈ Γ.map Prod.fst
  /-- Evaluate an exact law from values for only its declared dependencies. -/
  evalLawDeps :
    {Γ : Ctx Ty} → {τ : Ty} → (d : DistExpr Γ τ) →
      ((x : VarId) → (σ : Ty) → HasVar Γ x σ → x ∈ distDeps d → Val σ) →
        RationalLaw (Val τ)
  /-- Dependency-local expression evaluation agrees with full-environment
  evaluation when supplied by that environment. -/
  evalDeps_eq_eval :
    ∀ {Γ : Ctx Ty} {τ : Ty} (e : Expr Γ τ) (ρ : Env Val Γ),
      evalDeps e (fun x σ h _ => ρ x σ h) = eval e ρ
  /-- Dependency-local exact-law evaluation agrees with full-environment
  evaluation when supplied by that environment. -/
  evalLawDeps_eq_evalLaw :
    ∀ {Γ : Ctx Ty} {τ : Ty} (d : DistExpr Γ τ) (ρ : Env Val Γ),
      evalLawDeps d (fun x σ h _ => ρ x σ h) = evalLaw d ρ
  /-- Soundness of `exprDeps`: if two environments agree on the declared
  dependency set, `eval` produces equal results. The semantic justification
  for treating `exprDeps` as a usable dependency tracker. -/
  expr_deps_sound :
    ∀ {Γ : Ctx Ty} {τ : Ty} (e : Expr Γ τ) (ρ₁ ρ₂ : Env Val Γ),
      AgreesOn ρ₁ ρ₂ (exprDeps e) → eval e ρ₁ = eval e ρ₂
  /-- Soundness of `distDeps` for retained exact probability tables. -/
  law_deps_sound :
    ∀ {Γ : Ctx Ty} {τ : Ty} (d : DistExpr Γ τ) (ρ₁ ρ₂ : Env Val Γ),
      AgreesOn ρ₁ ρ₂ (distDeps d) → evalLaw d ρ₁ = evalLaw d ρ₂

namespace IExpr

/-- Denote a retained exact rational table as GameTheory's canonical semantic
finite probability law. -/
noncomputable def evalDist (L : IExpr) {Γ : Ctx L.Ty} {τ : L.Ty}
    (dist : L.DistExpr Γ τ) (env : Env L.Val Γ) : FinDist (L.Val τ) :=
  (L.evalLaw dist env).denote

/-- Dependency-local semantic distribution evaluation, derived from the
retained exact rational table. -/
noncomputable def evalDistDeps (L : IExpr) {Γ : Ctx L.Ty} {τ : L.Ty}
    (dist : L.DistExpr Γ τ)
    (env :
      (x : VarId) → (σ : L.Ty) → HasVar Γ x σ →
        x ∈ L.distDeps dist → L.Val σ) : FinDist (L.Val τ) :=
  (L.evalLawDeps dist env).denote

/-- Dependency-local and full-environment semantic laws agree because their
retained exact tables agree. -/
theorem evalDistDeps_eq_evalDist (L : IExpr)
    {Γ : Ctx L.Ty} {τ : L.Ty} (dist : L.DistExpr Γ τ)
    (env : Env L.Val Γ) :
    L.evalDistDeps dist (fun x σ h _ => env x σ h) =
      L.evalDist dist env := by
  unfold evalDistDeps evalDist
  rw [L.evalLawDeps_eq_evalLaw]

/-- Semantic distribution evaluation depends only on the declared
distribution dependencies. -/
theorem dist_deps_sound (L : IExpr)
    {Γ : Ctx L.Ty} {τ : L.Ty} (dist : L.DistExpr Γ τ)
    (left right : Env L.Val Γ)
    (hagrees : AgreesOn left right (L.distDeps dist)) :
    L.evalDist dist left = L.evalDist dist right := by
  unfold evalDist
  rw [L.law_deps_sound dist left right hagrees]

end IExpr

-- Promote the `decEqTy` and `decEqVal` interface fields to instances. After
-- this, `DecidableEq (L.Val τ)` is automatically available for any `L : IExpr`,
-- which makes typed values usable in executable finite tables downstream.
attribute [instance] IExpr.decEqTy IExpr.decEqVal


end Vegas
