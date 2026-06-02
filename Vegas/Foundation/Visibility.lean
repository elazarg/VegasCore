/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.ExprInterface

/-!
# Visibility-tagged contexts

`Visibility`, typed bindings `BindTy`, visibility contexts `VCtx`, the
intrinsic membership witness `VHasVar`, and visibility environments `VEnv`.
Each binding carries a base type plus visibility metadata.
-/

namespace Vegas

/-! ## Visibility-tagged contexts -/

/-- Visibility metadata for a binding.

This is deliberately separate from the binding's base type: reveal-like
operations change visibility, while the type associated with a variable name is
an immutable typing fact. The information model is *owner-or-all*: a secret
either belongs to one player, or it is visible to everyone. There is no
group-visibility constructor. -/
inductive Visibility (Player : Type) where
  | pub
  | hidden (owner : Player)
  deriving DecidableEq

namespace Visibility

/-- Owner recorded in visibility metadata, if the binding is hidden. -/
def owner {Player : Type} : Visibility Player → Option Player
  | .pub => none
  | .hidden owner => some owner

@[simp] theorem owner_pub {Player : Type} :
    owner (.pub : Visibility Player) = none := rfl

@[simp] theorem owner_hidden {Player : Type} (owner : Player) :
    Visibility.owner (.hidden owner) = some owner := rfl

/-- Can player `p` observe this visibility class? -/
def canSee {Player : Type} [DecidableEq Player]
    (p : Player) : Visibility Player → Bool
  | .pub => true
  | .hidden owner => decide (p = owner)

@[simp] theorem canSee_pub {Player : Type} [DecidableEq Player] (p : Player) :
    canSee p (.pub : Visibility Player) = true := rfl

@[simp] theorem canSee_hidden {Player : Type} [DecidableEq Player]
    (p owner : Player) :
    canSee p (.hidden owner : Visibility Player) = decide (p = owner) := rfl

end Visibility

/-- Visibility-aware binding type over an abstract language.

The representation is factored into an immutable `base` type and independent
visibility metadata. Code should construct bindings explicitly as
`⟨base, visibility⟩`, so places that change visibility do not look like they
also changed the underlying type. -/
structure BindTy (Player : Type) (L : IExpr) where
  base : L.Ty
  visibility : Visibility Player
  deriving DecidableEq

namespace BindTy

/-- Smart constructor for a public binding. -/
abbrev pub {Player : Type} {L : IExpr} (τ : L.Ty) : BindTy Player L :=
  ⟨τ, Visibility.pub⟩

/-- Smart constructor for a hidden binding owned by `owner`. -/
abbrev hidden {Player : Type} {L : IExpr} (owner : Player) (τ : L.Ty) :
    BindTy Player L :=
  ⟨τ, Visibility.hidden owner⟩

/-- Owner of a binding, if it is hidden. Public bindings have no owner. -/
abbrev owner {Player : Type} {L : IExpr} (τ : BindTy Player L) : Option Player :=
  τ.visibility.owner

/-- Whether a binding is statically public. -/
abbrev isPublic {Player : Type} {L : IExpr} (τ : BindTy Player L) : Prop :=
  τ.visibility = .pub

@[simp] theorem owner_public {Player : Type} {L : IExpr} (τ : L.Ty) :
    (.pub τ : BindTy Player L).owner = none := rfl

@[simp] theorem owner_hidden {Player : Type} {L : IExpr}
    (owner : Player) (τ : L.Ty) :
    (.hidden owner τ : BindTy Player L).owner = some owner := rfl

end BindTy

/-- Visibility-tagged contexts indexed by variable identifiers. -/
abbrev VCtx (Player : Type) (L : IExpr) : Type :=
  List (VarId × BindTy Player L)

/-- Typed membership in a visibility-tagged context. Definitionally
`HasVar Γ x τ` specialized to `Ctx (BindTy Player L)`; the abbreviation
preserves the readable name and the dot-notation namespace. -/
abbrev VHasVar {Player : Type} {L : IExpr}
    (Γ : VCtx Player L) (x : VarId) (τ : BindTy Player L) : Type :=
  HasVar Γ x τ

/-- The "head" position in a visibility context. -/
abbrev VHasVar.here {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L} : VHasVar ((x, τ) :: Γ) x τ :=
  HasVar.here

/-- Skip past a context entry to a position deeper in. -/
abbrev VHasVar.there {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x y : VarId} {τ τ' : BindTy Player L}
    (h : VHasVar Γ x τ) : VHasVar ((y, τ') :: Γ) x τ :=
  HasVar.there h

/-- Runtime environments for visibility-tagged contexts. -/
def VEnv {Player : Type} (L : IExpr) : VCtx Player L → Type :=
  fun Γ => ∀ x τ, VHasVar Γ x τ → L.Val τ.base

namespace VEnv

def empty {Player : Type} (L : IExpr) : VEnv (Player := Player) L [] :=
  fun _ _ h => nomatch h

def cons {Player : Type} {L : IExpr} {Γ : VCtx Player L} {x : VarId}
    {τ : BindTy Player L}
    (v : L.Val τ.base) (env : VEnv L Γ) :
    VEnv (Player := Player) L ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

theorem cons_ext {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L}
    {v₁ v₂ : L.Val τ.base} {env₁ env₂ : VEnv L Γ}
    (hv : v₁ = v₂) (henv : env₁ = env₂) :
    cons (x := x) v₁ env₁ = cons (x := x) v₂ env₂ := by
  subst hv; subst henv; rfl

theorem cons_head_eq_of_eq {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    {v₁ v₂ : L.Val τ.base} {env₁ env₂ : VEnv L Γ}
    (h : cons (x := x) v₁ env₁ = cons (x := x) v₂ env₂) :
    v₁ = v₂ := by
  exact congrFun (congrFun (congrFun h x) τ) VHasVar.here

theorem cons_tail_eq_of_eq {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    {v₁ v₂ : L.Val τ.base} {env₁ env₂ : VEnv L Γ}
    (h : cons (x := x) v₁ env₁ = cons (x := x) v₂ env₂) :
    env₁ = env₂ := by
  funext y σ hy
  exact congrFun (congrFun (congrFun h y) σ) (VHasVar.there hy)

def get {Player : Type} {L : IExpr} {Γ : VCtx Player L} {x : VarId}
    {τ : BindTy Player L}
    (env : VEnv L Γ) (h : VHasVar Γ x τ) :
    L.Val τ.base :=
  env x τ h

def tail {Player : Type} {L : IExpr} {Γ : VCtx Player L} {x : VarId}
    {τ : BindTy Player L}
    (env : VEnv L ((x, τ) :: Γ)) : VEnv L Γ :=
  fun y σ h => env y σ (VHasVar.there h)

@[simp] theorem tail_cons {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L}
    {v : L.Val τ.base} {env : VEnv L Γ} :
    tail (x := x) (τ := τ) (cons v env) = env := rfl

@[simp] theorem cons_get_here {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    {v : L.Val τ.base} {env : VEnv L Γ} :
    (VEnv.cons v env).get (VHasVar.here (Γ := Γ) (x := x) (τ := τ)) = v := rfl

@[simp] theorem cons_get_there {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x y : VarId} {τ σ : BindTy Player L}
    {v : L.Val τ.base} {env : VEnv L Γ}
    {h : VHasVar Γ y σ} :
    (VEnv.cons (x := x) v env).get (VHasVar.there h) = env.get h := rfl

/-- In a context with unique names, `VEnv.get` is proof-irrelevant:
the value depends only on `x` and `τ`, not on the `VHasVar` proof. The
visibility-aware analogue of `Env.get_eq_of_nodup`. -/
theorem get_eq_of_nodup {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L}
    (hnodup : (Γ.map Prod.fst).Nodup)
    (env : VEnv L Γ) (h₁ h₂ : VHasVar Γ x τ) :
    env.get h₁ = env.get h₂ := by
  rw [HasVar.eq_of_nodup hnodup h₁ h₂]

end VEnv


end Vegas
