/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.ExprInterface

/-!
# Concrete Vegas expression layer

This file fixes the concrete value types used by the current Vegas protocol
and defines the concrete expression and distribution syntax over plain
(non-visibility) contexts.
-/

noncomputable section

namespace Vegas

/-- The width of the concrete word type, matching an EVM machine word. -/
abbrev wordBits : Nat := 256

inductive BaseTy where
  | int : BaseTy
  | bool : BaseTy
  /-- An EVM machine word: `wordBits`-wide, with modular arithmetic. Unlike
  `int` this is a finite type, so it may be sampled, committed, and revealed,
  and it encodes into storage without loss. -/
  | word : BaseTy
  | range (lo hi : Int) : BaseTy
  | option (b : BaseTy) : BaseTy
  | result (b : BaseTy) : BaseTy
deriving Repr, DecidableEq

abbrev Val : BaseTy → Type
  | .int => Int
  | .bool => Bool
  | .word => BitVec wordBits
  | .range lo hi => Set.Icc lo hi
  | .option b => Option (Val b)
  | .result b => PublicationResult (Val b)

def instDecidableEqVal : (b : BaseTy) → DecidableEq (Val b)
  | .int => inferInstance
  | .bool => inferInstance
  | .word => inferInstance
  | .range _ _ => inferInstance
  | .option b =>
      letI : DecidableEq (Val b) := instDecidableEqVal b
      inferInstance
  | .result b =>
      letI : DecidableEq (Val b) := instDecidableEqVal b
      inferInstance

instance {b : BaseTy} : DecidableEq (Val b) := instDecidableEqVal b

def BaseTy.NonNullable : BaseTy → Prop
  | .option _ => False
  | .result _ => False
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

instance : CommitPayloadTy .word where
  nonNullable := trivial

instance : DefaultVal .word where
  defaultVal := 0

instance : DefaultVal .bool where
  defaultVal := false

instance (lo hi : Int) : CommitPayloadTy (.range lo hi) where
  nonNullable := trivial

noncomputable instance (lo hi : Int) [h : Nonempty (Val (.range lo hi))] :
    DefaultVal (.range lo hi) where
  defaultVal := Classical.choice h

/-- Plain (non-visibility) context over `BaseTy`. -/
abbrev CtxSimple : Type := Vegas.Ctx BaseTy

/-- Plain `Env` over concrete value types. -/
abbrev PlainEnv (Γ : CtxSimple) : Type := Vegas.Env Val Γ

inductive Expr : CtxSimple → BaseTy → Type where
  | var {Γ : CtxSimple} {b : BaseTy}
      (x : VarId) (h : HasVar Γ x b) : Expr Γ b
  | constInt {Γ : CtxSimple} (i : Int) : Expr Γ .int
  | constBool {Γ : CtxSimple} (b : Bool) : Expr Γ .bool
  | constWord {Γ : CtxSimple} (w : Val .word) : Expr Γ .word
  | constRange {Γ : CtxSimple} {lo hi : Int} (v : Val (.range lo hi)) :
      Expr Γ (.range lo hi)
  | none {Γ : CtxSimple} {b : BaseTy} : Expr Γ (.option b)
  | some {Γ : CtxSimple} {b : BaseTy} (e : Expr Γ b) : Expr Γ (.option b)
  | isSome {Γ : CtxSimple} {b : BaseTy} (e : Expr Γ (.option b)) : Expr Γ .bool
  | isNone {Γ : CtxSimple} {b : BaseTy} (e : Expr Γ (.option b)) : Expr Γ .bool
  | getD {Γ : CtxSimple} {b : BaseTy}
      (e : Expr Γ (.option b)) (fallback : Expr Γ b) :
      Expr Γ b
  | failure {Γ : CtxSimple} {b : BaseTy} : Expr Γ (.result b)
  | success {Γ : CtxSimple} {b : BaseTy} (e : Expr Γ b) : Expr Γ (.result b)
  | isSuccess {Γ : CtxSimple} {b : BaseTy}
      (e : Expr Γ (.result b)) : Expr Γ .bool
  | isFailure {Γ : CtxSimple} {b : BaseTy}
      (e : Expr Γ (.result b)) : Expr Γ .bool
  | getResultD {Γ : CtxSimple} {b : BaseTy}
      (e : Expr Γ (.result b)) (fallback : Expr Γ b) : Expr Γ b
  | addInt {Γ : CtxSimple} (l r : Expr Γ .int) : Expr Γ .int
  /-- EVM `ADD`: addition modulo `2 ^ wordBits`. -/
  | addWord {Γ : CtxSimple} (l r : Expr Γ .word) : Expr Γ .word
  /-- EVM `SUB`: subtraction modulo `2 ^ wordBits`. -/
  | subWord {Γ : CtxSimple} (l r : Expr Γ .word) : Expr Γ .word
  /-- EVM `MUL`: multiplication modulo `2 ^ wordBits`. -/
  | mulWord {Γ : CtxSimple} (l r : Expr Γ .word) : Expr Γ .word
  /-- EVM `LT`: unsigned comparison. -/
  | ltWord {Γ : CtxSimple} (l r : Expr Γ .word) : Expr Γ .bool
  | eq {Γ : CtxSimple} {b : BaseTy} (l r : Expr Γ b) : Expr Γ .bool
  | andBool {Γ : CtxSimple} (l r : Expr Γ .bool) : Expr Γ .bool
  | notBool {Γ : CtxSimple} (e : Expr Γ .bool) : Expr Γ .bool
  | ite {Γ : CtxSimple} {b : BaseTy}
      (c : Expr Γ .bool) (t f : Expr Γ b) : Expr Γ b

def evalExpr {Γ : CtxSimple} {b : BaseTy} : Expr Γ b → PlainEnv Γ → Val b
  | .var _ h, env => env.get h
  | .constInt i, _ => i
  | .constBool b, _ => b
  | .constWord w, _ => w
  | .constRange v, _ => v
  | .none, _ => none
  | .some e, env => some (evalExpr e env)
  | .isSome e, env => (evalExpr e env).isSome
  | .isNone e, env => (evalExpr e env).isNone
  | .getD e fallback, env => (evalExpr e env).getD (evalExpr fallback env)
  | .failure, _ => .failure
  | .success e, env => .success (evalExpr e env)
  | .isSuccess e, env => (evalExpr e env).isSuccess
  | .isFailure e, env => (evalExpr e env).isFailure
  | .getResultD e fallback, env =>
      (evalExpr e env).getD (evalExpr fallback env)
  | .addInt l r, env => evalExpr l env + evalExpr r env
  | .addWord l r, env => evalExpr l env + evalExpr r env
  | .subWord l r, env => evalExpr l env - evalExpr r env
  | .mulWord l r, env => evalExpr l env * evalExpr r env
  | .ltWord l r, env => (evalExpr l env).ult (evalExpr r env)
  | .eq l r, env => decide (evalExpr l env = evalExpr r env)
  | .andBool l r, env => evalExpr l env && evalExpr r env
  | .notBool e, env => !(evalExpr e env)
  | .ite c t f, env => if evalExpr c env then evalExpr t env else evalExpr f env

/-- Expression dependency set. -/
def exprDeps {Γ : CtxSimple} {b : BaseTy} : Expr Γ b → Finset VarId
  | .var x _ => {x}
  | .constInt _ => ∅
  | .constBool _ => ∅
  | .constWord _ => ∅
  | .constRange _ => ∅
  | .none => ∅
  | .some e => exprDeps e
  | .isSome e => exprDeps e
  | .isNone e => exprDeps e
  | .getD e fallback => exprDeps e ∪ exprDeps fallback
  | .failure => ∅
  | .success e => exprDeps e
  | .isSuccess e => exprDeps e
  | .isFailure e => exprDeps e
  | .getResultD e fallback => exprDeps e ∪ exprDeps fallback
  | .addInt l r => exprDeps l ∪ exprDeps r
  | .addWord l r => exprDeps l ∪ exprDeps r
  | .subWord l r => exprDeps l ∪ exprDeps r
  | .mulWord l r => exprDeps l ∪ exprDeps r
  | .ltWord l r => exprDeps l ∪ exprDeps r
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
  | constWord _ =>
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
  | failure =>
      intro y hy
      simp [exprDeps] at hy
  | success e ih =>
      intro y hy
      exact ih y hy
  | isSuccess e ih =>
      intro y hy
      exact ih y hy
  | isFailure e ih =>
      intro y hy
      exact ih y hy
  | getResultD e fallback ihe ihf =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihe y hy
      · exact ihf y hy
  | addInt l r ihl ihr =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihl y hy
      · exact ihr y hy
  | addWord l r ihl ihr =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihl y hy
      · exact ihr y hy
  | subWord l r ihl ihr =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihl y hy
      · exact ihr y hy
  | mulWord l r ihl ihr =>
      intro y hy
      rcases Finset.mem_union.mp (by simpa [exprDeps] using hy) with hy | hy
      · exact ihl y hy
      · exact ihr y hy
  | ltWord l r ihl ihr =>
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
  | constWord _ => rfl
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
  | failure => rfl
  | success e ih =>
    simp only [evalExpr]
    rw [ih ha]
  | isSuccess e ih =>
    simp only [evalExpr]
    rw [ih ha]
  | isFailure e ih =>
    simp only [evalExpr]
    rw [ih ha]
  | getResultD e fallback ihe ihf =>
    simp only [evalExpr]
    rw [ihe (ha.mono Finset.subset_union_left),
        ihf (ha.mono Finset.subset_union_right)]
  | addInt l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | addWord l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | subWord l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | mulWord l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | ltWord l r ihl ihr =>
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

def evalExprDeps {Γ : CtxSimple} {b : BaseTy} : (e : Expr Γ b) →
    ((x : VarId) → (τ : BaseTy) → HasVar Γ x τ →
      x ∈ exprDeps e → Val τ) → Val b
  | .var x h, ρ => ρ x _ h (by simp [exprDeps])
  | .constInt i, _ => i
  | .constBool b, _ => b
  | .constWord w, _ => w
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
  | .failure, _ => .failure
  | .success e, ρ =>
      .success (evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simpa [exprDeps] using hx)))
  | .isSuccess e, ρ =>
      (evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simpa [exprDeps] using hx))).isSuccess
  | .isFailure e, ρ =>
      (evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simpa [exprDeps] using hx))).isFailure
  | .getResultD e fallback, ρ =>
      (evalExprDeps e
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))).getD
        (evalExprDeps fallback
          (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])))
  | .addInt l r, ρ =>
      evalExprDeps l
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])) +
      evalExprDeps r
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))
  | .addWord l r, ρ =>
      evalExprDeps l
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])) +
      evalExprDeps r
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))
  | .subWord l r, ρ =>
      evalExprDeps l
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])) -
      evalExprDeps r
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))
  | .mulWord l r, ρ =>
      evalExprDeps l
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])) *
      evalExprDeps r
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))
  | .ltWord l r, ρ =>
      (evalExprDeps l
        (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx]))).ult
        (evalExprDeps r
          (fun x τ h hx => ρ x τ h (by simp [exprDeps, hx])))
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
  | constWord _ => rfl
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
  | failure => rfl
  | success e ih =>
      simp [evalExprDeps, evalExpr, ih]
  | isSuccess e ih =>
      simp [evalExprDeps, evalExpr, ih]
  | isFailure e ih =>
      simp [evalExprDeps, evalExpr, ih]
  | getResultD e fallback ihe ihf =>
      simp [evalExprDeps, evalExpr, ihe, ihf]
  | addInt l r ihl ihr =>
      simp [evalExprDeps, evalExpr, ihl, ihr]
  | addWord l r ihl ihr =>
      simp [evalExprDeps, evalExpr, ihl, ihr]
  | subWord l r ihl ihr =>
      simp [evalExprDeps, evalExpr, ihl, ihr]
  | mulWord l r ihl ihr =>
      simp [evalExprDeps, evalExpr, ihl, ihr]
  | ltWord l r ihl ihr =>
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
  | weighted (law : RationalLaw (Val b)) : DistExpr Γ b
  | ite (c : Expr Γ .bool) (t f : DistExpr Γ b) : DistExpr Γ b

def evalLawDistExpr {Γ : CtxSimple} {b : BaseTy} :
    DistExpr Γ b → PlainEnv Γ → RationalLaw (Val b)
  | .weighted law, _ => law
  | .ite c t f, env =>
      if evalExpr c env then evalLawDistExpr t env else evalLawDistExpr f env

/-- Distribution expression dependency set. -/
def distExprDeps {Γ : CtxSimple} {b : BaseTy} : DistExpr Γ b → Finset VarId
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

theorem law_deps_sound {Γ : CtxSimple} {b : BaseTy}
    (d : DistExpr Γ b) (ρ₁ ρ₂ : PlainEnv Γ)
    (ha : AgreesOn ρ₁ ρ₂ (distExprDeps d)) :
    evalLawDistExpr d ρ₁ = evalLawDistExpr d ρ₂ := by
  induction d with
  | weighted _ => rfl
  | ite c t f iht ihf =>
    simp only [evalLawDistExpr]
    rw [expr_deps_sound c ρ₁ ρ₂
      (ha.mono (Finset.subset_union_left.trans Finset.subset_union_left))]
    split
    · exact iht (ha.mono (Finset.subset_union_right.trans Finset.subset_union_left))
    · exact ihf (ha.mono Finset.subset_union_right)

def evalLawDistExprDeps {Γ : CtxSimple} {b : BaseTy} : (d : DistExpr Γ b) →
    ((x : VarId) → (τ : BaseTy) → HasVar Γ x τ →
      x ∈ distExprDeps d → Val τ) →
        RationalLaw (Val b)
  | .weighted law, _ => law
  | .ite c t f, ρ =>
      if evalExprDeps c
          (fun x τ h hx => ρ x τ h (by simp [distExprDeps, hx])) then
        evalLawDistExprDeps t
          (fun x τ h hx => ρ x τ h (by simp [distExprDeps, hx]))
      else
        evalLawDistExprDeps f
          (fun x τ h hx => ρ x τ h (by simp [distExprDeps, hx]))

theorem evalLawDistExprDeps_eq_evalLaw {Γ : CtxSimple} {b : BaseTy}
    (d : DistExpr Γ b) (ρ : PlainEnv Γ) :
    evalLawDistExprDeps d (fun x τ h _ => ρ x τ h) =
      evalLawDistExpr d ρ := by
  induction d with
  | weighted _ => rfl
  | ite c t f iht ihf =>
      simp [evalLawDistExprDeps, evalLawDistExpr,
        evalExprDeps_eq_eval, iht, ihf]

/-- The current concrete language, viewed as an instance of `IExpr`. -/
@[reducible] def simpleExpr : Vegas.IExpr where
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
  DistExpr := DistExpr
  evalLaw := @evalLawDistExpr
  distDeps := @distExprDeps
  dist_deps_context := @dist_deps_context
  evalLawDeps := @evalLawDistExprDeps
  evalDeps_eq_eval := @evalExprDeps_eq_eval
  evalLawDeps_eq_evalLaw := @evalLawDistExprDeps_eq_evalLaw
  expr_deps_sound := @expr_deps_sound
  law_deps_sound := @law_deps_sound

instance simpleExprResultTypes : IExpr.ResultTypes simpleExpr where
  result := BaseTy.result
  valueEquiv := fun _ => Equiv.refl _

def Expr.weaken {Γ : CtxSimple} {b : BaseTy} {x : VarId} {τ : BaseTy}
    (e : Expr Γ b) : Expr ((x, τ) :: Γ) b :=
  match e with
  | .var y h => .var y (.there h)
  | .constInt i => .constInt i
  | .constBool v => .constBool v
  | .constWord w => .constWord w
  | .constRange v => .constRange v
  | .none => .none
  | .some e => .some e.weaken
  | .isSome e => .isSome e.weaken
  | .isNone e => .isNone e.weaken
  | .getD e fallback => .getD e.weaken fallback.weaken
  | .failure => .failure
  | .success e => .success e.weaken
  | .isSuccess e => .isSuccess e.weaken
  | .isFailure e => .isFailure e.weaken
  | .getResultD e fallback => .getResultD e.weaken fallback.weaken
  | .addInt l r => .addInt l.weaken r.weaken
  | .addWord l r => .addWord l.weaken r.weaken
  | .subWord l r => .subWord l.weaken r.weaken
  | .mulWord l r => .mulWord l.weaken r.weaken
  | .ltWord l r => .ltWord l.weaken r.weaken
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
  | _, .constWord w => .constWord w
  | _, .constRange v => .constRange v
  | _, .none => .none
  | _, .some e => .some (e.substVars σ)
  | _, .isSome e => .isSome (e.substVars σ)
  | _, .isNone e => .isNone (e.substVars σ)
  | _, .getD e fallback => .getD (e.substVars σ) (fallback.substVars σ)
  | _, .failure => .failure
  | _, .success e => .success (e.substVars σ)
  | _, .isSuccess e => .isSuccess (e.substVars σ)
  | _, .isFailure e => .isFailure (e.substVars σ)
  | _, .getResultD e fallback =>
      .getResultD (e.substVars σ) (fallback.substVars σ)
  | _, .addInt l r => .addInt (l.substVars σ) (r.substVars σ)
  | _, .addWord l r => .addWord (l.substVars σ) (r.substVars σ)
  | _, .subWord l r => .subWord (l.substVars σ) (r.substVars σ)
  | _, .mulWord l r => .mulWord (l.substVars σ) (r.substVars σ)
  | _, .ltWord l r => .ltWord (l.substVars σ) (r.substVars σ)
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
  | _, .weighted law => .weighted law
  | _, .ite c t f =>
      .ite (c.substVars σ) (t.substVars σ) (f.substVars σ)

theorem evalExpr_weaken {Γ : CtxSimple} {b τ : BaseTy} {x : VarId}
    (e : Expr Γ b) (v : Val τ) (env : PlainEnv Γ) :
    evalExpr e.weaken (Env.cons (x := x) v env) = evalExpr e env := by
  induction e with
  | var _ _ => rfl
  | constInt _ => rfl
  | constBool _ => rfl
  | constWord _ => rfl
  | constRange _ => rfl
  | none => rfl
  | some e ih => simp [Expr.weaken, evalExpr, ih]
  | isSome e ih => simp [Expr.weaken, evalExpr, ih]
  | isNone e ih => simp [Expr.weaken, evalExpr, ih]
  | getD e fallback ihe ihf => simp [Expr.weaken, evalExpr, ihe, ihf]
  | failure => rfl
  | success e ih => simp [Expr.weaken, evalExpr, ih]
  | isSuccess e ih => simp [Expr.weaken, evalExpr, ih]
  | isFailure e ih => simp [Expr.weaken, evalExpr, ih]
  | getResultD e fallback ihe ihf =>
      simp [Expr.weaken, evalExpr, ihe, ihf]
  | addInt l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | addWord l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | subWord l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | mulWord l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | ltWord l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | eq l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | andBool l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | notBool e ih => simp [Expr.weaken, evalExpr, ih]
  | ite c t f ihc iht ihf => simp [Expr.weaken, evalExpr, ihc, iht, ihf]

private def Expr.constVal {Γ : CtxSimple} : {b : BaseTy} → Val b → Expr Γ b
  | .int, i => .constInt i
  | .bool, b => .constBool b
  | .word, w => .constWord w
  | .range _ _, v => .constRange v
  | .option _, Option.none => .none
  | .option _, Option.some v => .some (Expr.constVal v)
  | .result _, .failure => .failure
  | .result _, .success v => .success (Expr.constVal v)

private def Expr.replaceHeadWithGetD
    {Γ : CtxSimple} {x : VarId} {b c : BaseTy}
    (fallback : Val b) :
    Expr ((x, b) :: Γ) c → Expr ((x, .option b) :: Γ) c
  | .var _ .here =>
      .getD (.var x .here) (.constVal fallback)
  | .var z (.there h') =>
      .var z (.there h')
  | .constInt i => .constInt i
  | .constBool v => .constBool v
  | .constWord w => .constWord w
  | .constRange v => .constRange v
  | .none => .none
  | .some e => .some (e.replaceHeadWithGetD fallback)
  | .isSome e => .isSome (e.replaceHeadWithGetD fallback)
  | .isNone e => .isNone (e.replaceHeadWithGetD fallback)
  | .getD e fb =>
      .getD (e.replaceHeadWithGetD fallback)
        (fb.replaceHeadWithGetD fallback)
  | .failure => .failure
  | .success e => .success (e.replaceHeadWithGetD fallback)
  | .isSuccess e => .isSuccess (e.replaceHeadWithGetD fallback)
  | .isFailure e => .isFailure (e.replaceHeadWithGetD fallback)
  | .getResultD e fb =>
      .getResultD (e.replaceHeadWithGetD fallback)
        (fb.replaceHeadWithGetD fallback)
  | .addInt l r =>
      .addInt (l.replaceHeadWithGetD fallback)
        (r.replaceHeadWithGetD fallback)
  | .addWord l r =>
      .addWord (l.replaceHeadWithGetD fallback)
        (r.replaceHeadWithGetD fallback)
  | .subWord l r =>
      .subWord (l.replaceHeadWithGetD fallback)
        (r.replaceHeadWithGetD fallback)
  | .mulWord l r =>
      .mulWord (l.replaceHeadWithGetD fallback)
        (r.replaceHeadWithGetD fallback)
  | .ltWord l r =>
      .ltWord (l.replaceHeadWithGetD fallback)
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

private theorem evalExpr_constVal {Γ : CtxSimple} {b : BaseTy}
    (v : Val b) (env : PlainEnv Γ) :
    evalExpr (Expr.constVal v) env = v := by
  induction b with
  | int => simp [Expr.constVal, evalExpr]
  | bool => simp [Expr.constVal, evalExpr]
  | word => simp [Expr.constVal, evalExpr]
  | range lo hi => simp [Expr.constVal, evalExpr]
  | option b ih =>
      cases v with
      | none => simp [Expr.constVal, evalExpr]
      | some v =>
          simp [Expr.constVal, evalExpr, ih]
  | result b ih =>
      cases v with
      | failure => simp [Expr.constVal, evalExpr]
      | success v => simp [Expr.constVal, evalExpr, ih]

private theorem evalExpr_replaceHeadWithGetD_some
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
  | constWord w =>
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
  | failure =>
      simp [Expr.replaceHeadWithGetD, evalExpr]
  | success e ih =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ih]
  | isSuccess e ih =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ih]
  | isFailure e ih =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ih]
  | getResultD e fb ihe ihf =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihe, ihf]
  | addInt l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | addWord l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | subWord l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | mulWord l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | ltWord l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | eq l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | andBool l r ihl ihr =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihl, ihr]
  | notBool e ih =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ih]
  | ite c t f ihc iht ihf =>
      simp [Expr.replaceHeadWithGetD, evalExpr, ihc, iht, ihf]

/-- The absent value used by nullable surface commitments. It is an explicit
payload value; an execution model separately describes message submission and
silence. -/
private def declineValue (b : BaseTy) : Val (.option b) := Option.none

private def Expr.nullableCommitGuardWithFallback
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

/-- **A nullable commitment always accepts a decline.**  The guard is bypassed
outright when the payload is absent, so no program condition can make declining
illegal. -/
@[simp] theorem evalExpr_nullableCommitGuard_declineValue
    {Γ : CtxSimple} {x : VarId} {b : BaseTy} [DefaultVal b]
    (R : Expr ((x, b) :: Γ) .bool)
    (env : PlainEnv Γ) :
    evalExpr (Expr.nullableCommitGuard R)
        (Env.cons (x := x) (declineValue b) env) = true := by
  simp [Expr.nullableCommitGuard, Expr.nullableCommitGuardWithFallback, evalExpr,
    declineValue]

theorem evalExpr_nullableCommitGuard_some
    {Γ : CtxSimple} {x : VarId} {b : BaseTy} [DefaultVal b]
    (R : Expr ((x, b) :: Γ) .bool)
    (v : Val b) (env : PlainEnv Γ) :
    evalExpr (Expr.nullableCommitGuard R)
        (Env.cons (x := x) (some v) env) =
      evalExpr R (Env.cons (x := x) v env) := by
  simp [Expr.nullableCommitGuard, Expr.nullableCommitGuardWithFallback, evalExpr,
    evalExpr_replaceHeadWithGetD_some DefaultVal.defaultVal R v env]

@[simp] private theorem evalLawDistExpr_weighted {Γ : CtxSimple} {b : BaseTy}
    (law : RationalLaw (Val b)) (env : PlainEnv Γ) :
    evalLawDistExpr (.weighted law) env = law := rfl

private theorem evalLawDistExpr_ite_true {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : PlainEnv Γ}
    (hc : evalExpr c env = true) :
    evalLawDistExpr (.ite c t f) env = evalLawDistExpr t env := by
  simp [evalLawDistExpr, hc]

private theorem evalLawDistExpr_ite_false {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : PlainEnv Γ}
    (hc : evalExpr c env = false) :
    evalLawDistExpr (.ite c t f) env = evalLawDistExpr f env := by
  simp [evalLawDistExpr, hc]

def DistExpr.point {Γ : CtxSimple} {b : BaseTy}
    (v : Val b) : DistExpr Γ b := .weighted (.pure v)

end Vegas
