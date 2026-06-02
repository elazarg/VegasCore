/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Mathlib.Data.Int.Interval
import Vegas.Core.FiniteDomain

/-!
# Concrete Vegas expression layer

This file fixes the concrete value types used by the current Vegas protocol
and defines the concrete expression and distribution syntax over plain
(non-visibility) contexts.
-/

namespace Vegas

abbrev Player : Type := Nat

inductive BaseTy where
  | int : BaseTy
  | bool : BaseTy
  | range (lo hi : Int) : BaseTy
  | option (b : BaseTy) : BaseTy
deriving Repr, DecidableEq

abbrev Val : BaseTy → Type
  | .int => Int
  | .bool => Bool
  | .range lo hi => Set.Icc lo hi
  | .option b => Option (Val b)

def instDecidableEqVal : (b : BaseTy) → DecidableEq (Val b)
  | .int => inferInstance
  | .bool => inferInstance
  | .range _ _ => inferInstance
  | .option b =>
      letI : DecidableEq (Val b) := instDecidableEqVal b
      inferInstance

instance : DecidableEq (Val b) := instDecidableEqVal b

def BaseTy.NonNullable : BaseTy → Prop
  | .option _ => False
  | _ => True

class CommitPayloadTy (b : BaseTy) : Prop where
  nonNullable : b.NonNullable

class DefaultVal (b : BaseTy) where
  defaultVal : Val b

instance : CommitPayloadTy .int where
  nonNullable := trivial

instance : DefaultVal .int where
  defaultVal := 0

instance : CommitPayloadTy .bool where
  nonNullable := trivial

instance : DefaultVal .bool where
  defaultVal := false

instance (lo hi : Int) : CommitPayloadTy (.range lo hi) where
  nonNullable := trivial

noncomputable instance (lo hi : Int) [h : Nonempty (Val (.range lo hi))] :
    DefaultVal (.range lo hi) where
  defaultVal := Classical.choice h

theorem not_commitPayloadTy_option (b : BaseTy) :
    ¬ CommitPayloadTy (.option b) := by
  intro h
  exact h.nonNullable

/-- Plain (non-visibility) context over `BaseTy`. -/
abbrev CtxSimple : Type := Vegas.Ctx BaseTy

/-- Plain `Env` over concrete value types. -/
abbrev PlainEnv (Γ : CtxSimple) : Type := Vegas.Env Val Γ

inductive Expr : CtxSimple → BaseTy → Type where
  | var (x : VarId) (h : HasVar Γ x b) : Expr Γ b
  | constInt (i : Int) : Expr Γ .int
  | constBool (b : Bool) : Expr Γ .bool
  | constRange {lo hi : Int} (v : Val (.range lo hi)) :
      Expr Γ (.range lo hi)
  | none {b : BaseTy} : Expr Γ (.option b)
  | some {b : BaseTy} (e : Expr Γ b) : Expr Γ (.option b)
  | isSome {b : BaseTy} (e : Expr Γ (.option b)) : Expr Γ .bool
  | isNone {b : BaseTy} (e : Expr Γ (.option b)) : Expr Γ .bool
  | getD {b : BaseTy} (e : Expr Γ (.option b)) (fallback : Expr Γ b) :
      Expr Γ b
  | addInt (l r : Expr Γ .int) : Expr Γ .int
  | eq (l r : Expr Γ b) : Expr Γ .bool
  | andBool (l r : Expr Γ .bool) : Expr Γ .bool
  | notBool (e : Expr Γ .bool) : Expr Γ .bool
  | ite (c : Expr Γ .bool) (t f : Expr Γ b) : Expr Γ b

def evalExpr : Expr Γ b → PlainEnv Γ → Val b
  | .var _ h, env => env.get h
  | .constInt i, _ => i
  | .constBool b, _ => b
  | .constRange v, _ => v
  | .none, _ => none
  | .some e, env => some (evalExpr e env)
  | .isSome e, env => (evalExpr e env).isSome
  | .isNone e, env => (evalExpr e env).isNone
  | .getD e fallback, env => (evalExpr e env).getD (evalExpr fallback env)
  | .addInt l r, env => evalExpr l env + evalExpr r env
  | .eq l r, env => decide (evalExpr l env = evalExpr r env)
  | .andBool l r, env => evalExpr l env && evalExpr r env
  | .notBool e, env => !(evalExpr e env)
  | .ite c t f, env => if evalExpr c env then evalExpr t env else evalExpr f env

/-- Expression dependency set. -/
def exprDeps : Expr Γ b → Finset VarId
  | .var x _ => {x}
  | .constInt _ => ∅
  | .constBool _ => ∅
  | .constRange _ => ∅
  | .none => ∅
  | .some e => exprDeps e
  | .isSome e => exprDeps e
  | .isNone e => exprDeps e
  | .getD e fallback => exprDeps e ∪ exprDeps fallback
  | .addInt l r => exprDeps l ∪ exprDeps r
  | .eq l r => exprDeps l ∪ exprDeps r
  | .andBool l r => exprDeps l ∪ exprDeps r
  | .notBool e => exprDeps e
  | .ite c t f => exprDeps c ∪ exprDeps t ∪ exprDeps f

theorem expr_deps_context {Γ : CtxSimple} {b : BaseTy}
    (e : Expr Γ b) :
    ∀ x, x ∈ exprDeps e → x ∈ Γ.map Prod.fst := by
  induction e with
  | var x h =>
      intro y hy
      have hyx : y = x := Finset.mem_singleton.mp (by simpa [exprDeps] using hy)
      subst y
      exact HasVar.mem_map_fst h
  | constInt _ =>
      intro y hy
      simp [exprDeps] at hy
  | constBool _ =>
      intro y hy
      simp [exprDeps] at hy
  | constRange _ =>
      intro y hy
      simp [exprDeps] at hy
  | none =>
      intro y hy
      simp [exprDeps] at hy
  | some e ih =>
      intro y hy
      exact ih y hy
  | isSome e ih =>
      intro y hy
      exact ih y hy
  | isNone e ih =>
      intro y hy
      exact ih y hy
  | getD e fallback ihe ihf =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihe y hy
      · exact ihf y hy
  | addInt l r ihl ihr =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihl y hy
      · exact ihr y hy
  | eq l r ihl ihr =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihl y hy
      · exact ihr y hy
  | andBool l r ihl ihr =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihl y hy
      · exact ihr y hy
  | notBool e ih =>
      intro y hy
      exact ih y hy
  | ite c t f ihc iht ihf =>
      intro y hy
      have hy' :
          y ∈ exprDeps c ∨ y ∈ exprDeps t ∨ y ∈ exprDeps f := by
        simpa [exprDeps] using hy
      rcases hy' with hyc | htf
      · exact ihc y hyc
      · rcases htf with hyt | hyf
        · exact iht y hyt
        · exact ihf y hyf

theorem expr_deps_sound {Γ : CtxSimple} {b : BaseTy}
    (e : Expr Γ b) (ρ₁ ρ₂ : PlainEnv Γ)
    (ha : AgreesOn ρ₁ ρ₂ (exprDeps e)) :
    evalExpr e ρ₁ = evalExpr e ρ₂ := by
  induction e with
  | var x h =>
    exact ha x _ h (Finset.mem_singleton.mpr rfl)
  | constInt _ => rfl
  | constBool _ => rfl
  | constRange _ => rfl
  | none => rfl
  | some e ih =>
    simp only [evalExpr]
    rw [ih ha]
  | isSome e ih =>
    simp only [evalExpr]
    rw [ih ha]
  | isNone e ih =>
    simp only [evalExpr]
    rw [ih ha]
  | getD e fallback ihe ihf =>
    simp only [evalExpr]
    rw [ihe (ha.mono Finset.subset_union_left),
        ihf (ha.mono Finset.subset_union_right)]
  | addInt l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | eq l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | andBool l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | notBool e ih =>
    simp only [evalExpr]
    rw [ih ha]
  | ite c t f ihc iht ihf =>
    simp only [evalExpr]
    rw [ihc (ha.mono (Finset.subset_union_left.trans Finset.subset_union_left))]
    split
    · exact iht (ha.mono (Finset.subset_union_right.trans Finset.subset_union_left))
    · exact ihf (ha.mono Finset.subset_union_right)

def evalExprDeps : (e : Expr Γ b) →
    ((x : VarId) → (τ : BaseTy) → HasVar Γ x τ →
      x ∈ exprDeps e → Val τ) → Val b
  | .var x h, ρ => ρ x _ h (by simp [exprDeps])
  | .constInt i, _ => i
  | .constBool b, _ => b
  | .constRange v, _ => v
  | .none, _ => none
  | .some e, ρ =>
      some (evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simpa [exprDeps] using hx)))
  | .isSome e, ρ =>
      (evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simpa [exprDeps] using hx))).isSome
  | .isNone e, ρ =>
      (evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simpa [exprDeps] using hx))).isNone
  | .getD e fallback, ρ =>
      (evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))).getD
        (evalExprDeps fallback
          (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])))
  | .addInt l r, ρ =>
      evalExprDeps l
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])) +
      evalExprDeps r
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))
  | .eq l r, ρ =>
      decide
        (evalExprDeps l
            (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])) =
          evalExprDeps r
            (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])))
  | .andBool l r, ρ =>
      evalExprDeps l
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])) &&
      evalExprDeps r
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))
  | .notBool e, ρ =>
      !(evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simpa [exprDeps] using hx)))
  | .ite c t f, ρ =>
      if evalExprDeps c
          (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])) then
        evalExprDeps t
          (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))
      else
        evalExprDeps f
          (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))

theorem evalExprDeps_eq_eval {Γ : CtxSimple} {b : BaseTy}
    (e : Expr Γ b) (ρ : PlainEnv Γ) :
    evalExprDeps e (fun x τ h _ => ρ x τ h) = evalExpr e ρ := by
  induction e with
  | var x h => rfl
  | constInt _ => rfl
  | constBool _ => rfl
  | constRange _ => rfl
  | none => rfl
  | some e ih =>
      simp [evalExprDeps, evalExpr, ih]
  | isSome e ih =>
      simp [evalExprDeps, evalExpr, ih]
  | isNone e ih =>
      simp [evalExprDeps, evalExpr, ih]
  | getD e fallback ihe ihf =>
      simp [evalExprDeps, evalExpr, ihe, ihf]
  | addInt l r ihl ihr =>
      simp [evalExprDeps, evalExpr, ihl, ihr]
  | eq l r ihl ihr =>
      simp [evalExprDeps, evalExpr, ihl, ihr]
  | andBool l r ihl ihr =>
      simp [evalExprDeps, evalExpr, ihl, ihr]
  | notBool e ih =>
      simp [evalExprDeps, evalExpr, ih]
  | ite c t f ihc iht ihf =>
      simp [evalExprDeps, evalExpr, ihc, iht, ihf]

inductive DistExpr (Γ : CtxSimple) (b : BaseTy) : Type where
  | weighted (entries : List (Val b × ℚ≥0)) : DistExpr Γ b
  | ite (c : Expr Γ .bool) (t f : DistExpr Γ b) : DistExpr Γ b

def evalDistExpr : DistExpr Γ b → PlainEnv Γ → FWeight (Val b)
  | .weighted entries, _ => FWeight.ofList entries
  | .ite c t f, env =>
      if evalExpr c env then evalDistExpr t env else evalDistExpr f env

/-- Distribution expression dependency set. -/
def distExprDeps : DistExpr Γ b → Finset VarId
  | .weighted _ => ∅
  | .ite c t f => exprDeps c ∪ distExprDeps t ∪ distExprDeps f

theorem dist_deps_context {Γ : CtxSimple} {b : BaseTy}
    (d : DistExpr Γ b) :
    ∀ x, x ∈ distExprDeps d → x ∈ Γ.map Prod.fst := by
  induction d with
  | weighted _ =>
      intro x hx
      simp [distExprDeps] at hx
  | ite c t f iht ihf =>
      intro x hx
      have hx' :
          x ∈ exprDeps c ∨ x ∈ distExprDeps t ∨ x ∈ distExprDeps f := by
        simpa [distExprDeps] using hx
      rcases hx' with hxc | hrest
      · exact expr_deps_context c x hxc
      · rcases hrest with hxt | hxf
        · exact iht x hxt
        · exact ihf x hxf

theorem dist_deps_sound {Γ : CtxSimple} {b : BaseTy}
    (d : DistExpr Γ b) (ρ₁ ρ₂ : PlainEnv Γ)
    (ha : AgreesOn ρ₁ ρ₂ (distExprDeps d)) :
    evalDistExpr d ρ₁ = evalDistExpr d ρ₂ := by
  induction d with
  | weighted _ => rfl
  | ite c t f iht ihf =>
    simp only [evalDistExpr]
    rw [expr_deps_sound c ρ₁ ρ₂
      (ha.mono (Finset.subset_union_left.trans Finset.subset_union_left))]
    split
    · exact iht (ha.mono (Finset.subset_union_right.trans Finset.subset_union_left))
    · exact ihf (ha.mono Finset.subset_union_right)

def evalDistExprDeps : (d : DistExpr Γ b) →
    ((x : VarId) → (τ : BaseTy) → HasVar Γ x τ →
      x ∈ distExprDeps d → Val τ) → FWeight (Val b)
  | .weighted entries, _ => FWeight.ofList entries
  | .ite c t f, ρ =>
      if evalExprDeps c
          (fun x τ h hx => ρ x τ h (by simp [distExprDeps, hx])) then
        evalDistExprDeps t
          (fun x τ h hx => ρ x τ h (by simp [distExprDeps, hx]))
      else
        evalDistExprDeps f
          (fun x τ h hx => ρ x τ h (by simp [distExprDeps, hx]))

theorem evalDistExprDeps_eq_evalDist {Γ : CtxSimple} {b : BaseTy}
    (d : DistExpr Γ b) (ρ : PlainEnv Γ) :
    evalDistExprDeps d (fun x τ h _ => ρ x τ h) = evalDistExpr d ρ := by
  induction d with
  | weighted _ => rfl
  | ite c t f iht ihf =>
      simp [evalDistExprDeps, evalDistExpr, evalExprDeps_eq_eval, iht, ihf]

def Expr.weakenAfterHead
    {Γ : CtxSimple} {x y : VarId} {τ σ b : BaseTy}
    (e : Expr ((x, τ) :: Γ) b) : Expr ((x, τ) :: (y, σ) :: Γ) b :=
  match e with
  | .var _ .here => .var x .here
  | .var z (.there h') => .var z (.there (.there h'))
  | .constInt i => .constInt i
  | .constBool v => .constBool v
  | .constRange v => .constRange v
  | .none => .none
  | .some e => .some e.weakenAfterHead
  | .isSome e => .isSome e.weakenAfterHead
  | .isNone e => .isNone e.weakenAfterHead
  | .getD e fallback => .getD e.weakenAfterHead fallback.weakenAfterHead
  | .addInt l r => .addInt l.weakenAfterHead r.weakenAfterHead
  | .eq l r => .eq l.weakenAfterHead r.weakenAfterHead
  | .andBool l r => .andBool l.weakenAfterHead r.weakenAfterHead
  | .notBool e => .notBool e.weakenAfterHead
  | .ite c t f => .ite c.weakenAfterHead t.weakenAfterHead f.weakenAfterHead

theorem evalExpr_weakenAfterHead
    {Γ : CtxSimple} {x y : VarId} {τ σ b : BaseTy}
    (e : Expr ((x, τ) :: Γ) b)
    (vx : Val τ) (vy : Val σ) (env : PlainEnv Γ) :
    evalExpr e.weakenAfterHead (Env.cons (x := x) vx (Env.cons (x := y) vy env)) =
      evalExpr e (Env.cons (x := x) vx env) := by
  induction e with
  | var z h =>
      cases h <;> simp [Expr.weakenAfterHead, evalExpr]
  | constInt i =>
      simp [Expr.weakenAfterHead, evalExpr]
  | constBool v =>
      simp [Expr.weakenAfterHead, evalExpr]
  | constRange v =>
      simp [Expr.weakenAfterHead, evalExpr]
  | none =>
      simp [Expr.weakenAfterHead, evalExpr]
  | some e ih =>
      simp [Expr.weakenAfterHead, evalExpr, ih]
  | isSome e ih =>
      simp [Expr.weakenAfterHead, evalExpr, ih]
  | isNone e ih =>
      simp [Expr.weakenAfterHead, evalExpr, ih]
  | getD e fallback ihe ihf =>
      simp [Expr.weakenAfterHead, evalExpr, ihe, ihf]
  | addInt l r ihl ihr =>
      simp [Expr.weakenAfterHead, evalExpr, ihl, ihr]
  | eq l r ihl ihr =>
      simp [Expr.weakenAfterHead, evalExpr, ihl, ihr]
  | andBool l r ihl ihr =>
      simp [Expr.weakenAfterHead, evalExpr, ihl, ihr]
  | notBool e ih =>
      simp [Expr.weakenAfterHead, evalExpr, ih]
  | ite c t f ihc iht ihf =>
      simp [Expr.weakenAfterHead, evalExpr, ihc, iht, ihf]

private theorem not_mem_left_of_not_mem_union
    {α : Type} [DecidableEq α] {a : α} {s t : Finset α}
    (h : a ∉ s ∪ t) : a ∉ s :=
  fun hs => h (Finset.mem_union_left t hs)

private theorem not_mem_right_of_not_mem_union
    {α : Type} [DecidableEq α] {a : α} {s t : Finset α}
    (h : a ∉ s ∪ t) : a ∉ t :=
  fun ht => h (Finset.mem_union_right s ht)

def Expr.dropAfterHead
    {Γ : CtxSimple} {x y : VarId} {τ σ b : BaseTy}
    (e : Expr ((x, τ) :: (y, σ) :: Γ) b)
    (hy : y ∉ exprDeps e) : Expr ((x, τ) :: Γ) b :=
  match e with
  | .var _ .here => .var x .here
  | .var _ (.there .here) => False.elim (hy (by simp [exprDeps]))
  | .var z (.there (.there h')) => .var z (.there h')
  | .constInt i => .constInt i
  | .constBool v => .constBool v
  | .constRange v => .constRange v
  | .none => .none
  | .some e =>
      .some (e.dropAfterHead (by simpa [exprDeps] using hy))
  | .isSome e =>
      .isSome (e.dropAfterHead (by simpa [exprDeps] using hy))
  | .isNone e =>
      .isNone (e.dropAfterHead (by simpa [exprDeps] using hy))
  | .getD e fallback =>
      have hy' : y ∉ exprDeps e ∪ exprDeps fallback := by
        simpa [exprDeps] using hy
      .getD
        (e.dropAfterHead (not_mem_left_of_not_mem_union hy'))
        (fallback.dropAfterHead (not_mem_right_of_not_mem_union hy'))
  | .addInt l r =>
      have hy' : y ∉ exprDeps l ∪ exprDeps r := by
        simpa [exprDeps] using hy
      .addInt
        (l.dropAfterHead (not_mem_left_of_not_mem_union hy'))
        (r.dropAfterHead (not_mem_right_of_not_mem_union hy'))
  | .eq l r =>
      have hy' : y ∉ exprDeps l ∪ exprDeps r := by
        simpa [exprDeps] using hy
      .eq
        (l.dropAfterHead (not_mem_left_of_not_mem_union hy'))
        (r.dropAfterHead (not_mem_right_of_not_mem_union hy'))
  | .andBool l r =>
      have hy' : y ∉ exprDeps l ∪ exprDeps r := by
        simpa [exprDeps] using hy
      .andBool
        (l.dropAfterHead (not_mem_left_of_not_mem_union hy'))
        (r.dropAfterHead (not_mem_right_of_not_mem_union hy'))
  | .notBool e =>
      .notBool (e.dropAfterHead (by simpa [exprDeps] using hy))
  | .ite c t f =>
      have hy' : y ∉ exprDeps c ∪ exprDeps t ∪ exprDeps f := by
        simpa [exprDeps] using hy
      .ite
        (c.dropAfterHead
          (not_mem_left_of_not_mem_union
            (not_mem_left_of_not_mem_union hy')))
        (t.dropAfterHead
          (not_mem_right_of_not_mem_union
            (not_mem_left_of_not_mem_union hy')))
        (f.dropAfterHead (not_mem_right_of_not_mem_union hy'))

theorem evalExpr_dropAfterHead
    {Γ : CtxSimple} {x y : VarId} {τ σ b : BaseTy}
    (e : Expr ((x, τ) :: (y, σ) :: Γ) b)
    (hy : y ∉ exprDeps e)
    (vx : Val τ) (vy : Val σ) (env : PlainEnv Γ) :
    evalExpr (e.dropAfterHead hy) (Env.cons (x := x) vx env) =
      evalExpr e (Env.cons (x := x) vx (Env.cons (x := y) vy env)) := by
  induction e generalizing vx vy env with
  | var z h =>
      cases h with
      | here =>
          simp [Expr.dropAfterHead, evalExpr]
      | there h =>
          cases h with
          | here =>
              exfalso
              exact hy (by simp [exprDeps])
          | there h' =>
              simp [Expr.dropAfterHead, evalExpr]
  | constInt i =>
      simp [Expr.dropAfterHead, evalExpr]
  | constBool v =>
      simp [Expr.dropAfterHead, evalExpr]
  | constRange v =>
      simp [Expr.dropAfterHead, evalExpr]
  | none =>
      simp [Expr.dropAfterHead, evalExpr]
  | some e ih =>
      simp only [Expr.dropAfterHead, evalExpr]
      rw [ih (by
            intro hmem
            apply hy
            simpa [exprDeps] using hmem)]
  | isSome e ih =>
      simp only [Expr.dropAfterHead, evalExpr]
      rw [ih (by
            intro hmem
            apply hy
            simpa [exprDeps] using hmem)]
  | isNone e ih =>
      simp only [Expr.dropAfterHead, evalExpr]
      rw [ih (by
            intro hmem
            apply hy
            simpa [exprDeps] using hmem)]
  | getD e fallback ihe ihf =>
      simp only [Expr.dropAfterHead, evalExpr]
      rw [ihe (by
            intro hmem
            apply hy
            simp [exprDeps, hmem]),
          ihf (by
            intro hmem
            apply hy
            simp [exprDeps, hmem])]
  | addInt l r ihl ihr =>
      simp only [Expr.dropAfterHead, evalExpr]
      rw [ihl (by
            intro hmem
            apply hy
            simp [exprDeps, hmem]),
          ihr (by
            intro hmem
            apply hy
            simp [exprDeps, hmem])]
  | eq l r ihl ihr =>
      simp only [Expr.dropAfterHead, evalExpr, decide_eq_decide]
      rw [ihl (by
            intro hmem
            apply hy
            simp [exprDeps, hmem]),
          ihr (by
            intro hmem
            apply hy
            simp [exprDeps, hmem])]
  | andBool l r ihl ihr =>
      simp only [Expr.dropAfterHead, evalExpr]
      rw [ihl (by
            intro hmem
            apply hy
            simp [exprDeps, hmem]),
          ihr (by
            intro hmem
            apply hy
            simp [exprDeps, hmem])]
  | notBool e ih =>
      simp only [Expr.dropAfterHead, evalExpr, Bool.not_eq_eq_eq_not, Bool.not_not]
      rw [ih (by
            intro hmem
            apply hy
            simpa [exprDeps] using hmem)]
  | ite c t f ihc iht ihf =>
      have hyc : y ∉ exprDeps c := by
        intro hmem
        apply hy
        simp [exprDeps, hmem]
      have hyt : y ∉ exprDeps t := by
        intro hmem
        apply hy
        simp [exprDeps, hmem]
      have hyf : y ∉ exprDeps f := by
        intro hmem
        apply hy
        simp [exprDeps, hmem]
      cases hcv : evalExpr c (Env.cons (x := x) vx (Env.cons (x := y) vy env)) with
      | false =>
          have hcv' : evalExpr (c.dropAfterHead hyc) (Env.cons (x := x) vx env) = false := by
            rw [ihc hyc vx vy env, hcv]
          simp only [Expr.dropAfterHead, evalExpr, hcv', Bool.false_eq_true, ↓reduceIte, hcv]
          exact ihf hyf vx vy env
      | true =>
          have hcv' : evalExpr (c.dropAfterHead hyc) (Env.cons (x := x) vx env) = true := by
            rw [ihc hyc vx vy env, hcv]
          simp only [Expr.dropAfterHead, evalExpr, hcv', ↓reduceIte, hcv]
          exact iht hyt vx vy env

/-- The current concrete language, viewed as an instance of `IExpr`. -/
def simpleExpr : Vegas.IExpr where
  Ty := BaseTy
  decEqTy := inferInstance
  Val := Val
  decEqVal := by intro τ; cases τ <;> infer_instance
  bool := .bool
  toBool := id
  int := .int
  toInt := id
  Expr := Expr
  eval := @evalExpr
  exprDeps := @exprDeps
  evalDeps := @evalExprDeps
  expr_deps_context := @expr_deps_context
  extendAfterHead := by
    intro Γ x y τ σ b e
    refine ⟨e.weakenAfterHead, ?_⟩
    intro vx vy env
    exact evalExpr_weakenAfterHead e vx vy env
  dropAfterHead := by
    intro Γ x y τ σ b e hy
    refine ⟨e.dropAfterHead hy, ?_⟩
    intro vx vy env
    exact evalExpr_dropAfterHead e hy vx vy env
  DistExpr := DistExpr
  evalDist := @evalDistExpr
  distDeps := @distExprDeps
  dist_deps_context := @dist_deps_context
  evalDistDeps := @evalDistExprDeps
  evalDeps_eq_eval := @evalExprDeps_eq_eval
  evalDistDeps_eq_evalDist := @evalDistExprDeps_eq_evalDist
  expr_deps_sound := @expr_deps_sound
  dist_deps_sound := @dist_deps_sound

noncomputable instance finiteType_bool : FiniteType simpleExpr .bool where
  fintype := by
    change Fintype Bool
    infer_instance

noncomputable instance finiteType_range (lo hi : Int) :
    FiniteType simpleExpr (.range lo hi) where
  fintype := by
    change Fintype (Set.Icc lo hi)
    infer_instance

noncomputable instance finiteType_option (b : BaseTy)
    [FiniteType simpleExpr b] : FiniteType simpleExpr (.option b) where
  fintype := by
    letI : Fintype (Val b) := FiniteType.fintype (L := simpleExpr) (τ := b)
    change Fintype (Option (Val b))
    infer_instance

abbrev BindTySimple : Type := Vegas.BindTy Player simpleExpr
abbrev VCtxSimple : Type := Vegas.VCtx Player simpleExpr
abbrev VHasVarSimple : VCtxSimple → VarId → BindTySimple → Type :=
  Vegas.VHasVar
abbrev VEnvSimple (Γ : VCtxSimple) : Type :=
  Vegas.VEnv (Player := Player) simpleExpr Γ

namespace BindTySimple

abbrev base : BindTySimple → BaseTy := Vegas.BindTy.base

end BindTySimple

namespace VHasVarSimple

abbrev here {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple} :
    VHasVarSimple ((x, τ) :: Γ) x τ :=
  Vegas.VHasVar.here

abbrev there {Γ : VCtxSimple} {x y : VarId} {τ τ' : BindTySimple}
    (h : VHasVarSimple Γ x τ) : VHasVarSimple ((y, τ') :: Γ) x τ :=
  Vegas.VHasVar.there h

end VHasVarSimple

namespace VEnvSimple

abbrev empty : VEnvSimple [] :=
  Vegas.VEnv.empty (Player := Player) simpleExpr

abbrev cons {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple}
    (v : Val τ.base) (env : VEnvSimple Γ) : VEnvSimple ((x, τ) :: Γ) :=
  Vegas.VEnv.cons v env

abbrev get {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple}
    (env : VEnvSimple Γ) (h : VHasVarSimple Γ x τ) : Val τ.base :=
  Vegas.VEnv.get env h

@[simp] theorem cons_get_here {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple}
    {v : Val τ.base} {env : VEnvSimple Γ} :
    (VEnvSimple.cons v env).get
      (VHasVarSimple.here (Γ := Γ) (x := x) (τ := τ)) = v := by
  exact Vegas.VEnv.cons_get_here

@[simp] theorem cons_get_there {Γ : VCtxSimple} {x y : VarId}
    {τ σ : BindTySimple}
    {v : Val τ.base} {env : VEnvSimple Γ}
    {h : VHasVarSimple Γ y σ} :
    (VEnvSimple.cons (x := x) v env).get (VHasVarSimple.there h) =
      env.get h := by
  exact Vegas.VEnv.cons_get_there

abbrev toView (p : Player) {Γ : VCtxSimple} (env : VEnvSimple Γ) :
    VEnvSimple (Vegas.viewVCtx p Γ) :=
  Vegas.VEnv.toView p env

abbrev toPub {Γ : VCtxSimple} (env : VEnvSimple Γ) :
    VEnvSimple (Vegas.pubVCtx Γ) :=
  Vegas.VEnv.toPub env

end VEnvSimple

namespace VHasVarSimple

abbrev ofViewVCtx {p : Player} {Γ : VCtxSimple} {x : VarId}
    {τ : BindTySimple} :
    VHasVarSimple (Vegas.viewVCtx p Γ) x τ → VHasVarSimple Γ x τ :=
  Vegas.VHasVar.ofViewVCtx (p := p)

abbrev ofPubVCtx {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple} :
    VHasVarSimple (Vegas.pubVCtx Γ) x τ → VHasVarSimple Γ x τ :=
  Vegas.VHasVar.ofPubVCtx

end VHasVarSimple

def Expr.weaken {Γ : CtxSimple} {b : BaseTy} {x : VarId} {τ : BaseTy}
    (e : Expr Γ b) : Expr ((x, τ) :: Γ) b :=
  match e with
  | .var y h => .var y (.there h)
  | .constInt i => .constInt i
  | .constBool v => .constBool v
  | .constRange v => .constRange v
  | .none => .none
  | .some e => .some e.weaken
  | .isSome e => .isSome e.weaken
  | .isNone e => .isNone e.weaken
  | .getD e fallback => .getD e.weaken fallback.weaken
  | .addInt l r => .addInt l.weaken r.weaken
  | .eq l r => .eq l.weaken r.weaken
  | .andBool l r => .andBool l.weaken r.weaken
  | .notBool e => .notBool e.weaken
  | .ite c t f => .ite c.weaken t.weaken f.weaken

/-- Substitute every variable in an expression through a typed expression
environment. -/
def Expr.substVars {Γ Δ : CtxSimple}
    (σ : {x : VarId} → {b : BaseTy} → HasVar Γ x b → Expr Δ b) :
    {b : BaseTy} → Expr Γ b → Expr Δ b
  | _, .var _ h => σ h
  | _, .constInt i => .constInt i
  | _, .constBool v => .constBool v
  | _, .constRange v => .constRange v
  | _, .none => .none
  | _, .some e => .some (e.substVars σ)
  | _, .isSome e => .isSome (e.substVars σ)
  | _, .isNone e => .isNone (e.substVars σ)
  | _, .getD e fallback => .getD (e.substVars σ) (fallback.substVars σ)
  | _, .addInt l r => .addInt (l.substVars σ) (r.substVars σ)
  | _, .eq l r => .eq (l.substVars σ) (r.substVars σ)
  | _, .andBool l r => .andBool (l.substVars σ) (r.substVars σ)
  | _, .notBool e => .notBool (e.substVars σ)
  | _, .ite c t f =>
      .ite (c.substVars σ) (t.substVars σ) (f.substVars σ)

/-- Substitute every variable in a distribution through a typed expression
environment. -/
def DistExpr.substVars {Γ Δ : CtxSimple}
    (σ : {x : VarId} → {b : BaseTy} → HasVar Γ x b → Expr Δ b) :
    {b : BaseTy} → DistExpr Γ b → DistExpr Δ b
  | _, .weighted entries => .weighted entries
  | _, .ite c t f =>
      .ite (c.substVars σ) (t.substVars σ) (f.substVars σ)

/-- Reinterpret a public expression in a player's visible erased context. -/
def Expr.publicToView {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr} {b : BaseTy} (who : P)
    (e : Expr (erasePubVCtx Γ) b) :
    Expr (eraseVCtx (viewVCtx who Γ)) b :=
  e.substVars fun {x} {_} h => .var x (HasVar.pubToView (p := who) h)

theorem evalExpr_weaken {Γ : CtxSimple} {b τ : BaseTy} {x : VarId}
    (e : Expr Γ b) (v : Val τ) (env : PlainEnv Γ) :
    evalExpr e.weaken (Env.cons (x := x) v env) = evalExpr e env := by
  induction e with
  | var _ _ => rfl
  | constInt _ => rfl
  | constBool _ => rfl
  | constRange _ => rfl
  | none => rfl
  | some e ih => simp [Expr.weaken, evalExpr, ih]
  | isSome e ih => simp [Expr.weaken, evalExpr, ih]
  | isNone e ih => simp [Expr.weaken, evalExpr, ih]
  | getD e fallback ihe ihf => simp [Expr.weaken, evalExpr, ihe, ihf]
  | addInt l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | eq l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | andBool l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | notBool e ih => simp [Expr.weaken, evalExpr, ih]
  | ite c t f ihc iht ihf => simp [Expr.weaken, evalExpr, ihc, iht, ihf]

def Expr.constVal {Γ : CtxSimple} : {b : BaseTy} → Val b → Expr Γ b
  | .int, i => .constInt i
  | .bool, b => .constBool b
  | .range _ _, v => .constRange v
  | .option _, Option.none => .none
  | .option _, Option.some v => .some (Expr.constVal v)

def Expr.replaceHeadWithGetD
    {Γ : CtxSimple} {x : VarId} {b c : BaseTy}
    (fallback : Val b) :
    Expr ((x, b) :: Γ) c → Expr ((x, .option b) :: Γ) c
  | .var _ .here =>
      .getD (.var x .here) (.constVal fallback)
  | .var z (.there h') =>
      .var z (.there h')
  | .constInt i => .constInt i
  | .constBool v => .constBool v
  | .constRange v => .constRange v
  | .none => .none
  | .some e => .some (e.replaceHeadWithGetD fallback)
  | .isSome e => .isSome (e.replaceHeadWithGetD fallback)
  | .isNone e => .isNone (e.replaceHeadWithGetD fallback)
  | .getD e fb =>
      .getD (e.replaceHeadWithGetD fallback)
        (fb.replaceHeadWithGetD fallback)
  | .addInt l r =>
      .addInt (l.replaceHeadWithGetD fallback)
        (r.replaceHeadWithGetD fallback)
  | .eq l r =>
      .eq (l.replaceHeadWithGetD fallback)
        (r.replaceHeadWithGetD fallback)
  | .andBool l r =>
      .andBool (l.replaceHeadWithGetD fallback)
        (r.replaceHeadWithGetD fallback)
  | .notBool e =>
      .notBool (e.replaceHeadWithGetD fallback)
  | .ite c t f =>
      .ite (c.replaceHeadWithGetD fallback)
        (t.replaceHeadWithGetD fallback)
        (f.replaceHeadWithGetD fallback)

theorem evalExpr_constVal {Γ : CtxSimple} {b : BaseTy}
    (v : Val b) (env : PlainEnv Γ) :
    evalExpr (Expr.constVal v) env = v := by
  induction b with
  | int => simp [Expr.constVal, evalExpr]
  | bool => simp [Expr.constVal, evalExpr]
  | range lo hi => simp [Expr.constVal, evalExpr]
  | option b ih =>
      cases v with
      | none => simp [Expr.constVal, evalExpr]
      | some v =>
          simp [Expr.constVal, evalExpr, ih]

theorem evalExpr_replaceHeadWithGetD_some
    {Γ : CtxSimple} {x : VarId} {b c : BaseTy}
    (fallback : Val b) (e : Expr ((x, b) :: Γ) c)
    (v : Val b) (env : PlainEnv Γ) :
    evalExpr (e.replaceHeadWithGetD fallback)
        (Env.cons (x := x) (some v) env) =
      evalExpr e (Env.cons (x := x) v env) := by
  induction e with
  | var z h =>
      cases h <;> simp [Expr.replaceHeadWithGetD, evalExpr, evalExpr_constVal]
  | constInt i =>
      simp [Expr.replaceHeadWithGetD, evalExpr]
  | constBool v =>
      simp [Expr.replaceHeadWithGetD, evalExpr]
  | constRange v =>
      simp [Expr.replaceHeadWithGetD, evalExpr]
  | none =>
      simp [Expr.replaceHeadWithGetD, evalExpr]
  | some e ih =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ih]
  | isSome e ih =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ih]
  | isNone e ih =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ih]
  | getD e fb ihe ihf =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihe, ihf]
  | addInt l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | eq l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | andBool l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | notBool e ih =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ih]
  | ite c t f ihc iht ihf =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihc, iht, ihf]

def Expr.nullableCommitGuardWithFallback
    {Γ : CtxSimple} {x : VarId} {b : BaseTy}
    (fallback : Val b) (R : Expr ((x, b) :: Γ) .bool) :
    Expr ((x, .option b) :: Γ) .bool :=
  .ite (.isNone (.var x .here)) (.constBool true)
    (R.replaceHeadWithGetD fallback)

def Expr.nullableCommitGuard
    {Γ : CtxSimple} {x : VarId} {b : BaseTy} [DefaultVal b]
    (R : Expr ((x, b) :: Γ) .bool) :
    Expr ((x, .option b) :: Γ) .bool :=
  Expr.nullableCommitGuardWithFallback DefaultVal.defaultVal R

@[simp] theorem evalExpr_nullableCommitGuard_none
    {Γ : CtxSimple} {x : VarId} {b : BaseTy} [DefaultVal b]
    (R : Expr ((x, b) :: Γ) .bool)
    (env : PlainEnv Γ) :
    evalExpr (Expr.nullableCommitGuard R)
        (Env.cons (x := x) Option.none env) = true := by
  simp [Expr.nullableCommitGuard, Expr.nullableCommitGuardWithFallback, evalExpr]

theorem evalExpr_nullableCommitGuard_some
    {Γ : CtxSimple} {x : VarId} {b : BaseTy} [DefaultVal b]
    (R : Expr ((x, b) :: Γ) .bool)
    (v : Val b) (env : PlainEnv Γ) :
    evalExpr (Expr.nullableCommitGuard R)
        (Env.cons (x := x) (some v) env) =
      evalExpr R (Env.cons (x := x) v env) := by
  simp [Expr.nullableCommitGuard, Expr.nullableCommitGuardWithFallback, evalExpr,
    evalExpr_replaceHeadWithGetD_some DefaultVal.defaultVal R v env]

theorem nullableCommitGuard_satisfiable
    {P : Type} [DecidableEq P] {Γ : VCtx P simpleExpr}
    {x : VarId} {b : BaseTy} [DefaultVal b]
    (R : Expr ((x, b) :: eraseVCtx Γ) .bool) :
    ∀ env : Env Val (eraseVCtx Γ),
      ∃ a : Val (.option b),
        Vegas.evalGuard (Player := P) (L := simpleExpr)
          (Expr.nullableCommitGuard R) a env = true := by
  intro env
  refine ⟨Option.none, ?_⟩
  change evalExpr (Expr.nullableCommitGuard R)
      (Env.cons (x := x) Option.none env) = true
  simp

/-- Extract variable IDs referenced by an expression (as a list). -/
def exprVars : Expr Γ b → List VarId
  | .var x _ => [x]
  | .constInt _ => []
  | .constBool _ => []
  | .constRange _ => []
  | .none => []
  | .some e => exprVars e
  | .isSome e => exprVars e
  | .isNone e => exprVars e
  | .getD e fallback => exprVars e ++ exprVars fallback
  | .addInt l r => exprVars l ++ exprVars r
  | .eq l r => exprVars l ++ exprVars r
  | .andBool l r => exprVars l ++ exprVars r
  | .notBool e => exprVars e
  | .ite c t f => exprVars c ++ exprVars t ++ exprVars f

/-- Extract variable IDs referenced by a distribution expression (as a list). -/
def distExprVars : DistExpr Γ b → List VarId
  | .weighted _ => []
  | .ite c t f => exprVars c ++ distExprVars t ++ distExprVars f

@[simp] theorem evalDistExpr_weighted {Γ : CtxSimple} {b : BaseTy}
    (entries : List (Val b × ℚ≥0)) (env : PlainEnv Γ) :
    evalDistExpr (.weighted entries) env = FWeight.ofList entries := rfl

theorem evalDistExpr_ite_true {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : PlainEnv Γ}
    (hc : evalExpr c env = true) :
    evalDistExpr (.ite c t f) env = evalDistExpr t env := by
  simp [evalDistExpr, hc]

theorem evalDistExpr_ite_false {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : PlainEnv Γ}
    (hc : evalExpr c env = false) :
    evalDistExpr (.ite c t f) env = evalDistExpr f env := by
  simp [evalDistExpr, hc]

def DistExpr.point (v : Val b) : DistExpr Γ b := .weighted [(v, 1)]

def DistExpr.uniform (vs : List (Val b)) : DistExpr Γ b :=
  let w : ℚ≥0 := 1 / (vs.length : ℚ≥0)
  .weighted (vs.map fun v => (v, w))

end Vegas
