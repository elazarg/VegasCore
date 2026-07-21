/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.Context

/-!
# The embedded expression-language interface `IExpr`

`IExpr` packages the concrete expression layer: types, values, expression and
distribution syntax, evaluation, dependency tracking, and the soundness laws
that justify treating `exprDeps` as a static over-approximation of semantic
dependence. Everything else in Vegas is generic over this interface.
-/

namespace Vegas

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
  /-- Denotational evaluation of a distribution into `FWeight (Val τ)`. -/
  evalDist : {Γ : Ctx Ty} → {τ : Ty} →
    DistExpr Γ τ → Env Val Γ → @FWeight (Val τ) decEqVal
  /-- Static over-approximation of variables a distribution reads. -/
  distDeps : {Γ : Ctx Ty} → {τ : Ty} → DistExpr Γ τ → Finset VarId
  /-- Distribution dependency sets mention only variables available in the
  distribution context. -/
  dist_deps_context :
    ∀ {Γ : Ctx Ty} {τ : Ty} (d : DistExpr Γ τ),
      ∀ x, x ∈ distDeps d → x ∈ Γ.map Prod.fst
  /-- Evaluate a distribution from values for only its declared dependencies. -/
  evalDistDeps :
    {Γ : Ctx Ty} → {τ : Ty} → (d : DistExpr Γ τ) →
      ((x : VarId) → (σ : Ty) → HasVar Γ x σ → x ∈ distDeps d → Val σ) →
        @FWeight (Val τ) decEqVal
  /-- Dependency-local expression evaluation agrees with full-environment
  evaluation when supplied by that environment. -/
  evalDeps_eq_eval :
    ∀ {Γ : Ctx Ty} {τ : Ty} (e : Expr Γ τ) (ρ : Env Val Γ),
      evalDeps e (fun x σ h _ => ρ x σ h) = eval e ρ
  /-- Dependency-local distribution evaluation agrees with full-environment
  evaluation when supplied by that environment. -/
  evalDistDeps_eq_evalDist :
    ∀ {Γ : Ctx Ty} {τ : Ty} (d : DistExpr Γ τ) (ρ : Env Val Γ),
      evalDistDeps d (fun x σ h _ => ρ x σ h) = evalDist d ρ
  /-- Soundness of `exprDeps`: if two environments agree on the declared
  dependency set, `eval` produces equal results. The semantic justification
  for treating `exprDeps` as a usable dependency tracker. -/
  expr_deps_sound :
    ∀ {Γ : Ctx Ty} {τ : Ty} (e : Expr Γ τ) (ρ₁ ρ₂ : Env Val Γ),
      AgreesOn ρ₁ ρ₂ (exprDeps e) → eval e ρ₁ = eval e ρ₂
  /-- Soundness of `distDeps`. -/
  dist_deps_sound :
    ∀ {Γ : Ctx Ty} {τ : Ty} (d : DistExpr Γ τ) (ρ₁ ρ₂ : Env Val Γ),
      AgreesOn ρ₁ ρ₂ (distDeps d) → evalDist d ρ₁ = evalDist d ρ₂

-- Promote the `decEqTy` and `decEqVal` interface fields to instances. After
-- this, `DecidableEq (L.Val τ)` is automatically available for any `L : IExpr`,
-- which is what lets `FWeight (L.Val τ)` and similar `Finsupp`-backed
-- constructions type-check downstream.
attribute [instance] IExpr.decEqTy IExpr.decEqVal


end Vegas
