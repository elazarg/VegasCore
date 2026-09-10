/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Obligations

/-! # Recall through source-environment extension

These lemmas are the local induction steps for comparing two written-order
source executions at the same structural suffix. Equality of a player's
current visible environment always recalls equality before the newest binding.
For public bindings, and for that player's own sealed bindings, it also recalls
equality of the newly chosen value. Another player's sealed value remains
unconstrained, exactly as source visibility requires.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Env

/-- Equality of extended plain environments recalls their newest values. -/
theorem cons_head_eq_of_eq {Γ : Ctx L.Ty} {x : VarId} {b : L.Ty}
    {leftValue rightValue : L.Val b} {left right : Env L.Val Γ}
    (h : Env.cons (x := x) leftValue left = Env.cons (x := x) rightValue right) :
    leftValue = rightValue := by
  exact congrFun (congrFun (congrFun h x) b) HasVar.here

/-- Equality of extended plain environments recalls the preceding environment. -/
theorem cons_tail_eq_of_eq {Γ : Ctx L.Ty} {x : VarId} {b : L.Ty}
    {leftValue rightValue : L.Val b} {left right : Env L.Val Γ}
    (h : Env.cons (x := x) leftValue left = Env.cons (x := x) rightValue right) :
    left = right := by
  funext y c hy
  exact congrFun (congrFun (congrFun h y) c) (HasVar.there hy)

end Env

namespace VEnv

omit [DecidableEq P] in
private theorem eraseEnv_injective {Γ : VCtx P L} {left right : VEnv L Γ}
    (h : left.eraseEnv = right.eraseEnv) : left = right := by
  funext x τ hx
  have hlookup := congrFun (congrFun (congrFun h x) τ.base) hx.toErased
  simpa using hlookup

private def visibleHere {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    (who : P) (hvisible : canSee who τ = true) :
    VHasVar (viewVCtx who ((x, τ) :: Γ)) x τ := by
  simp only [viewVCtx, hvisible, if_true]
  exact .here

private def visibleThere {Γ : VCtx P L} {x y : VarId} {τ σ : BindTy P L}
    (who : P) (hvisible : canSee who τ = true)
    (h : VHasVar (viewVCtx who Γ) y σ) :
    VHasVar (viewVCtx who ((x, τ) :: Γ)) y σ := by
  simp only [viewVCtx, hvisible, if_true]
  exact .there h

private def hiddenThere {Γ : VCtx P L} {x y : VarId} {τ σ : BindTy P L}
    (who : P) (hhidden : canSee who τ = false)
    (h : VHasVar (viewVCtx who Γ) y σ) :
    VHasVar (viewVCtx who ((x, τ) :: Γ)) y σ := by
  simp only [viewVCtx, hhidden]
  exact h

private theorem eraseView_cons_visible_recall {Γ : VCtx P L} {x : VarId}
    {τ : BindTy P L} (who : P) (hvisible : canSee who τ = true)
    (hctx : WFCtx ((x, τ) :: Γ))
    {leftValue rightValue : L.Val τ.base} {left right : VEnv L Γ}
    (hcurrent :
      ((VEnv.cons (x := x) (τ := τ) leftValue left).toView who).eraseEnv =
        ((VEnv.cons (x := x) (τ := τ) rightValue right).toView who).eraseEnv) :
    leftValue = rightValue ∧
      (left.toView who).eraseEnv = (right.toView who).eraseEnv := by
  have hview := eraseEnv_injective hcurrent
  let head := visibleHere (Γ := Γ) (x := x) who hvisible
  have hhead := congrFun (congrFun (congrFun hview x) τ) head
  have hheadProof : head.ofViewVCtx = VHasVar.here :=
    HasVar.eq_of_nodup hctx _ _
  change (VEnv.cons leftValue left) x τ head.ofViewVCtx =
    (VEnv.cons rightValue right) x τ head.ofViewVCtx at hhead
  rw [hheadProof] at hhead
  refine ⟨hhead, congrArg VEnv.eraseEnv ?_⟩
  funext y σ hy
  let extended := visibleThere (x := x) who hvisible hy
  have hvalue := congrFun (congrFun (congrFun hview y) σ) extended
  have hproof : extended.ofViewVCtx = VHasVar.there hy.ofViewVCtx :=
    HasVar.eq_of_nodup hctx _ _
  change (VEnv.cons leftValue left) y σ extended.ofViewVCtx =
    (VEnv.cons rightValue right) y σ extended.ofViewVCtx at hvalue
  rw [hproof] at hvalue
  exact hvalue

/-- A public source step recalls both its public draw and the preceding visible
environment from equality of the current source-visible environments. -/
theorem eraseView_cons_public_recall {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (who : P) (hctx : WFCtx ((x, .pub b) :: Γ))
    {leftValue rightValue : L.Val b} {left right : VEnv L Γ}
    (hcurrent :
      ((VEnv.cons (x := x) (τ := BindTy.pub b) leftValue left).toView who).eraseEnv =
        ((VEnv.cons (x := x) (τ := BindTy.pub b) rightValue right).toView who).eraseEnv) :
    leftValue = rightValue ∧
      (left.toView who).eraseEnv = (right.toView who).eraseEnv :=
  eraseView_cons_visible_recall who rfl hctx hcurrent

/-- An owner's sealed source step recalls both its choice and the preceding
visible environment. -/
theorem eraseView_cons_owned_recall {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (who : P) (hctx : WFCtx ((x, .sealed who b) :: Γ))
    {leftValue rightValue : L.Val b} {left right : VEnv L Γ}
    (hcurrent :
      ((VEnv.cons (x := x) (τ := BindTy.sealed who b) leftValue left).toView who).eraseEnv =
        ((VEnv.cons (x := x) (τ := BindTy.sealed who b) rightValue right).toView who).eraseEnv) :
    leftValue = rightValue ∧
      (left.toView who).eraseEnv = (right.toView who).eraseEnv := by
  apply eraseView_cons_visible_recall (τ := BindTy.sealed who b) who
  · simp [canSee, Visibility.canSee]
  · exact hctx
  · exact hcurrent

/-- Another player's sealed source step recalls the preceding visible
environment while leaving the hidden values unconstrained. -/
theorem eraseView_cons_other_recall {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {owner observer : P} (hother : observer ≠ owner)
    (hctx : WFCtx ((x, .sealed owner b) :: Γ))
    {leftValue rightValue : L.Val b} {left right : VEnv L Γ}
    (hcurrent :
      ((VEnv.cons (x := x) (τ := BindTy.sealed owner b) leftValue left).toView
          observer).eraseEnv =
        ((VEnv.cons (x := x) (τ := BindTy.sealed owner b) rightValue right).toView
          observer).eraseEnv) :
    (left.toView observer).eraseEnv = (right.toView observer).eraseEnv := by
  have hhidden : canSee observer (BindTy.sealed owner b) = false := by
    simp [canSee, Visibility.canSee, hother]
  have hview := eraseEnv_injective hcurrent
  apply congrArg VEnv.eraseEnv
  funext y σ hy
  let extended := hiddenThere (x := x) observer hhidden hy
  have hvalue := congrFun (congrFun (congrFun hview y) σ) extended
  have hproof : extended.ofViewVCtx = VHasVar.there hy.ofViewVCtx :=
    HasVar.eq_of_nodup hctx _ _
  change (VEnv.cons leftValue left) y σ extended.ofViewVCtx =
    (VEnv.cons rightValue right) y σ extended.ofViewVCtx at hvalue
  rw [hproof] at hvalue
  exact hvalue

end VEnv

end Vegas

/-- info: 'Vegas.VEnv.eraseView_cons_other_recall' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.VEnv.eraseView_cons_other_recall
