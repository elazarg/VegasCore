/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Scope

/-!
# Finite Infrastructure

Finite-enumeration instances for Vegas environments under program-local
finite-domain evidence.

This file intentionally stops at environments. Finite strategic-form
construction happens in the fixed-program modules instead.
-/

namespace Vegas

namespace Env

/-- The empty plain environment is equivalent to `Unit`. -/
def emptyEquivUnit {L : IExpr} :
    Env L.Val ([] : Ctx L.Ty) ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => Env.empty L.Val
  left_inv := by
    intro env
    funext x τ h
    nomatch h
  right_inv := by
    intro u
    cases u
    rfl

/-- A nonempty plain environment splits into its head value and tail
environment. -/
def consEquiv {L : IExpr} {Γ : Ctx L.Ty} {x : VarId} {τ : L.Ty} :
    Env L.Val ((x, τ) :: Γ) ≃ (L.Val τ × Env L.Val Γ) where
  toFun := fun env => (env x τ .here, fun y σ h => env y σ (.there h))
  invFun := fun ve => Env.cons ve.1 ve.2
  left_inv := by
    intro env
    funext y σ h
    cases h with
    | here => rfl
    | there h' => rfl
  right_inv := by
    intro ve
    cases ve
    rfl

@[reducible] noncomputable def instFintypeOfProof
    {L : IExpr} :
    {Γ : Ctx L.Ty} → FiniteCtxProof Γ → Fintype (Env L.Val Γ)
  | [], .nil =>
      Fintype.ofEquiv Unit emptyEquivUnit.symm
  | (_x, τ) :: Γ, .cons hτ hΓ =>
      let _ : Fintype (L.Val τ) := hτ.fintype
      let _ : Fintype (Env L.Val Γ) := instFintypeOfProof hΓ
      Fintype.ofEquiv (L.Val τ × Env L.Val Γ) consEquiv.symm

noncomputable instance instFintype
    {L : IExpr} {Γ : Ctx L.Ty} [hΓ : FiniteCtx Γ] :
    Fintype (Env L.Val Γ) :=
  instFintypeOfProof hΓ.proof

end Env

namespace VEnv

/-- The empty visibility environment is equivalent to `Unit`. -/
def emptyEquivUnit {Player : Type} {L : IExpr} :
    VEnv (Player := Player) L [] ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => VEnv.empty L
  left_inv := by
    intro env
    funext x τ h
    nomatch h
  right_inv := by
    intro u
    cases u
    rfl

/-- A nonempty visibility environment splits into its head value and tail
environment. -/
def consEquiv {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L} :
    VEnv (Player := Player) L ((x, τ) :: Γ) ≃
      (L.Val τ.base × VEnv L Γ) where
  toFun := fun env => (env x τ .here, fun y σ h => env y σ (.there h))
  invFun := fun ve => VEnv.cons ve.1 ve.2
  left_inv := by
    intro env
    funext y σ h
    cases h with
    | here => rfl
    | there h' => rfl
  right_inv := by
    intro ve
    cases ve
    rfl

@[reducible] noncomputable def instFintypeOfProof
    {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → FiniteVCtxProof Γ → Fintype (VEnv L Γ)
  | [], .nil =>
      Fintype.ofEquiv Unit emptyEquivUnit.symm
  | (_x, τ) :: Γ, .cons hτ hΓ =>
      let _ : Fintype (L.Val τ.base) := hτ.fintype
      let _ : Fintype (VEnv L Γ) := instFintypeOfProof hΓ
      Fintype.ofEquiv (L.Val τ.base × VEnv L Γ) consEquiv.symm

noncomputable instance instFintype
    {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    [hΓ : FiniteVCtx Γ] :
    Fintype (VEnv L Γ) :=
  instFintypeOfProof hΓ.proof

end VEnv

end Vegas
