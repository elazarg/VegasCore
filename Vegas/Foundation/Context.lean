/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.FWeight

/-!
# Plain typed contexts

Variable ids, plain typed contexts `Ctx`, the intrinsically-typed membership
witness `HasVar`, plain environments `Env`, and the `AgreesOn` dependency
vocabulary. This is the visibility-free substrate the rest of `Foundation`
builds on.
-/

namespace Vegas

/-! ## Plain typed contexts -/

/-- Variable identifiers for both plain and visibility-tagged contexts. -/
abbrev VarId : Type := Nat

/-- A plain typed context indexed by variable identifiers. -/
abbrev Ctx (Ty : Type) := List (VarId × Ty)

/-- Typed membership in a plain context. -/
inductive HasVar {Ty : Type} : Ctx Ty → VarId → Ty → Type where
  | here {Γ x τ} : HasVar ((x, τ) :: Γ) x τ
  | there {Γ x y τ τ'} : HasVar Γ x τ → HasVar ((y, τ') :: Γ) x τ

/-- Runtime environments for plain contexts. -/
def Env {Ty : Type} (Val : Ty → Type) : Ctx Ty → Type :=
  fun Γ => ∀ x τ, HasVar Γ x τ → Val τ

/-- A `HasVar` proof witnesses that `x` appears in the context's name list. -/
theorem HasVar.mem_map_fst {Ty : Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (h : HasVar Γ x τ) : x ∈ Γ.map Prod.fst := by
  induction h with
  | here => simp
  | there _ ih => simp [ih]

/-- In a context with unique names, `HasVar` is a subsingleton:
any two proofs of `HasVar Γ x τ` are equal. -/
theorem HasVar.eq_of_nodup {Ty : Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (hnodup : (Γ.map Prod.fst).Nodup)
    (h₁ h₂ : HasVar Γ x τ) : h₁ = h₂ := by
  induction h₁ with
  | @here Γ' y σ =>
    cases h₂ with
    | here => rfl
    | @there _ _ _ _ σ' h₂' =>
      have hnd := List.nodup_cons.mp hnodup
      exact absurd h₂'.mem_map_fst hnd.1
  | @there Γ' y z σ σ' h₁' ih =>
    cases h₂ with
    | @here =>
      have hnd := List.nodup_cons.mp hnodup
      exact absurd h₁'.mem_map_fst hnd.1
    | @there _ _ _ _ _ h₂' =>
      have hnd := List.nodup_cons.mp hnodup
      exact congrArg HasVar.there (ih hnd.2 h₂')

/-- In a context with unique names, `HasVar` determines the type:
if `HasVar Γ x τ₁` and `HasVar Γ x τ₂`, then `τ₁ = τ₂`. -/
theorem HasVar.type_unique {Ty : Type} {Γ : Ctx Ty} {x : VarId} {τ₁ τ₂ : Ty}
    (hnodup : (Γ.map Prod.fst).Nodup)
    (h₁ : HasVar Γ x τ₁) (h₂ : HasVar Γ x τ₂) : τ₁ = τ₂ := by
  induction h₁ with
  | here =>
    cases h₂ with
    | here => rfl
    | there h₂' =>
      exact absurd h₂'.mem_map_fst (List.nodup_cons.mp hnodup).1
  | there h₁' ih =>
    cases h₂ with
    | here =>
      exact absurd h₁'.mem_map_fst (List.nodup_cons.mp hnodup).1
    | there h₂' =>
      exact ih (List.nodup_cons.mp hnodup).2 h₂'

/-- In a context with unique names, `Env` lookups are proof-irrelevant:
the value depends only on `x` and `τ`, not on the `HasVar` proof. -/
theorem Env.get_eq_of_nodup {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x : VarId} {τ : Ty}
    (hnodup : (Γ.map Prod.fst).Nodup)
    (env : Env Val Γ) (h₁ h₂ : HasVar Γ x τ) :
    env x τ h₁ = env x τ h₂ := by
  rw [HasVar.eq_of_nodup hnodup h₁ h₂]

/-- Construct a `HasVar` from list membership. Recurses on the context and
case-splits on entry equality at each step, so `[DecidableEq Ty]` is needed
to extract computational data from the `Prop`-valued membership proof. The
sole in-tree call site has `Ty = L.Ty` for `L : IExpr`, where `decEqTy` is
already an instance. -/
def HasVar.ofMem {Ty : Type} [DecidableEq Ty] {Γ : Ctx Ty}
    {x : VarId} {τ : Ty} (h : (x, τ) ∈ Γ) : HasVar Γ x τ := by
  induction Γ with
  | nil => exact absurd h (by simp)
  | cons a Γ' ih =>
    by_cases heq : a = (x, τ)
    · subst heq; exact .here
    · exact .there (ih (List.mem_of_ne_of_mem (Ne.symm heq) h))

namespace Env

def empty {Ty : Type} (Val : Ty → Type) : Env Val ([] : Ctx Ty) :=
  fun _ _ h => nomatch h

def cons {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (v : Val τ) (env : Env Val Γ) : Env Val ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

def get {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (env : Env Val Γ) (h : HasVar Γ x τ) : Val τ :=
  env x τ h

@[simp] theorem cons_get_here {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x : VarId} {τ : Ty} {v : Val τ} {env : Env Val Γ} :
    (Env.cons v env).get (HasVar.here (x := x)) = v := rfl

@[simp] theorem cons_get_there {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x y : VarId} {τ σ : Ty} {v : Val τ} {env : Env Val Γ}
    {h : HasVar Γ y σ} :
    (Env.cons (x := x) v env).get (HasVar.there h) = env.get h := rfl

theorem cons_ext {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x : VarId} {τ : Ty}
    {v₁ v₂ : Val τ} {env₁ env₂ : Env Val Γ}
    (hv : v₁ = v₂) (henv : env₁ = env₂) :
    cons (x := x) v₁ env₁ = cons (x := x) v₂ env₂ := by
  subst hv; subst henv; rfl

end Env

/-! ## Variable agreement and dependency vocabulary -/

/-- Two environments agree on a set of variable identifiers. The vocabulary
in which `IExpr`'s dependency-soundness laws are phrased: if two environments
agree on `exprDeps e`, then `e` evaluates the same way in both. The
visibility-aware specialization `ObsEq` (defined in `Scope.lean`) restricts
the agreement set to the variables visible to a given player. -/
def AgreesOn {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    (ρ₁ ρ₂ : Env Val Γ) (xs : Finset VarId) : Prop :=
  ∀ x τ (h : HasVar Γ x τ), x ∈ xs → ρ₁ x τ h = ρ₂ x τ h

/-- Narrowing the agreement set preserves agreement. -/
theorem AgreesOn.mono {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {ρ₁ ρ₂ : Env Val Γ} {S T : Finset VarId}
    (h : AgreesOn ρ₁ ρ₂ T) (hST : S ⊆ T) : AgreesOn ρ₁ ρ₂ S :=
  fun x τ hx hm => h x τ hx (hST hm)


end Vegas
