/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Foundation.Basic

/-! # Finite expression domains and typed contexts

Opt-in finite-domain evidence for expression values and contexts. This interface
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

/-- The finite branching factor of a finite expression-language type. -/
noncomputable def finiteDomainSize (L : IExpr) (τ : L.Ty)
    [FiniteType L τ] : Nat :=
  Fintype.card (L.Val τ)

/-- A canonical encoding of finite expression-language values as `Fin`. -/
noncomputable def encodeFiniteType (L : IExpr) (τ : L.Ty)
    [FiniteType L τ] :
    L.Val τ ≃ Fin (finiteDomainSize L τ) :=
  Fintype.equivFin (L.Val τ)

/-- Structural evidence that every value stored in a plain context has a
finite domain. -/
inductive FiniteCtxProof {L : IExpr} : Ctx L.Ty → Type where
  | nil : FiniteCtxProof []
  | cons {x : VarId} {τ : L.Ty} {Γ : Ctx L.Ty}
      (head : FiniteType L τ) (tail : FiniteCtxProof Γ) :
      FiniteCtxProof ((x, τ) :: Γ)

/-- Typeclass wrapper for finite plain contexts. -/
class FiniteCtx {L : IExpr} (Γ : Ctx L.Ty) where
  proof : FiniteCtxProof Γ

instance finiteCtx_nil {L : IExpr} : FiniteCtx ([] : Ctx L.Ty) where
  proof := .nil

instance finiteCtx_cons {L : IExpr} {x : VarId} {τ : L.Ty}
    {Γ : Ctx L.Ty} [FiniteType L τ] [FiniteCtx Γ] :
    FiniteCtx ((x, τ) :: Γ) where
  proof := .cons (inferInstance : FiniteType L τ) (FiniteCtx.proof (Γ := Γ))

namespace FiniteCtxProof

@[reducible] noncomputable def fintypeOfHasVar {L : IExpr} :
    {Γ : Ctx L.Ty} → FiniteCtxProof Γ →
      {x : VarId} → {τ : L.Ty} → HasVar Γ x τ → Fintype (L.Val τ)
  | _, .nil, _, _, h => nomatch h
  | _, .cons head _tail, _, _, .here => head.fintype
  | _, .cons _head tail, _, _, .there h => fintypeOfHasVar tail h

end FiniteCtxProof

namespace FiniteCtx

@[reducible] noncomputable def fintypeOfHasVar {L : IExpr} {Γ : Ctx L.Ty}
    [hΓ : FiniteCtx Γ] {x : VarId} {τ : L.Ty}
    (h : HasVar Γ x τ) : Fintype (L.Val τ) :=
  FiniteCtxProof.fintypeOfHasVar hΓ.proof h

end FiniteCtx

/-- Structural evidence that every value stored in a visibility context has a
finite domain. -/
inductive FiniteVCtxProof {P : Type} {L : IExpr} :
    VCtx P L → Type where
  | nil : FiniteVCtxProof []
  | cons {x : VarId} {τ : BindTy P L} {Γ : VCtx P L}
      (head : FiniteType L τ.base) (tail : FiniteVCtxProof Γ) :
      FiniteVCtxProof ((x, τ) :: Γ)

/-- Typeclass wrapper for finite visibility contexts. -/
class FiniteVCtx {P : Type} {L : IExpr} (Γ : VCtx P L) where
  proof : FiniteVCtxProof Γ

instance finiteVCtx_nil {P : Type} {L : IExpr} :
    FiniteVCtx ([] : VCtx P L) where
  proof := .nil

instance finiteVCtx_cons {P : Type} {L : IExpr} {x : VarId}
    {τ : BindTy P L} {Γ : VCtx P L}
    [FiniteType L τ.base] [FiniteVCtx Γ] :
    FiniteVCtx ((x, τ) :: Γ) where
  proof := .cons (inferInstance : FiniteType L τ.base)
    (FiniteVCtx.proof (Γ := Γ))

namespace FiniteVCtxProof

@[reducible] noncomputable def fintypeOfHasVar {P : Type} {L : IExpr} :
    {Γ : VCtx P L} → FiniteVCtxProof Γ →
      {x : VarId} → {τ : BindTy P L} →
        VHasVar Γ x τ → Fintype (L.Val τ.base)
  | _, .nil, _, _, h => nomatch h
  | _, .cons head _tail, _, _, .here => head.fintype
  | _, .cons _head tail, _, _, .there h => fintypeOfHasVar tail h

def erase {P : Type} {L : IExpr} :
    {Γ : VCtx P L} → FiniteVCtxProof Γ →
      FiniteCtxProof (eraseVCtx Γ)
  | [], .nil => .nil
  | (_x, _τ) :: _Γ, .cons head tail => .cons head tail.erase

def view {P : Type} [DecidableEq P] {L : IExpr} (who : P) :
    {Γ : VCtx P L} → FiniteVCtxProof Γ →
      FiniteVCtxProof (viewVCtx who Γ)
  | [], .nil => .nil
  | (_x, _τ) :: _Γ, .cons head tail => by
      simp only [viewVCtx]
      split
      · exact .cons head (tail.view who)
      · exact tail.view who

end FiniteVCtxProof

namespace FiniteVCtx

@[reducible] noncomputable def fintypeOfHasVar {P : Type} {L : IExpr}
    {Γ : VCtx P L} [hΓ : FiniteVCtx Γ]
    {x : VarId} {τ : BindTy P L}
    (h : VHasVar Γ x τ) : Fintype (L.Val τ.base) :=
  FiniteVCtxProof.fintypeOfHasVar hΓ.proof h

@[reducible] def erase {P : Type} {L : IExpr} {Γ : VCtx P L}
    [hΓ : FiniteVCtx Γ] : FiniteCtx (eraseVCtx Γ) where
  proof := hΓ.proof.erase

@[reducible] def view {P : Type} [DecidableEq P] {L : IExpr}
    {Γ : VCtx P L} [hΓ : FiniteVCtx Γ] (who : P) :
    FiniteVCtx (viewVCtx who Γ) where
  proof := hΓ.proof.view who

end FiniteVCtx

end Vegas
