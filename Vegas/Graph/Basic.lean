/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Foundation.DeferredGuard
import Vegas.Foundation.Visibility

/-! # Typed immutable event graphs -/

namespace Vegas

namespace Graph

open Interaction

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]

/-- A publication-valued input to a retained guard. `pending` is useful for a
guard subject that has not yet been proposed; fields are otherwise immutable. -/
inductive GuardRead (Γ : VCtx Player L) : L.Ty → Type where
  | pending {τ : L.Ty} : GuardRead Γ τ
  | publicData {field : VarId} {τ : L.Ty}
      (source : HasVar Γ field (.pub τ)) : GuardRead Γ τ
  | publication {field : VarId} {τ : L.Ty}
      (source : HasVar Γ field (.pub (R.result τ))) : GuardRead Γ τ

namespace GuardRead

def get {Γ : VCtx Player L} {τ : L.Ty} :
    GuardRead (R := R) Γ τ → VEnv L Γ → Publication (L.Val τ)
  | .pending, _ => .pending
  | .publicData source, env => .value (env.get source)
  | .publication source, env =>
      match R.valueEquiv _ (env.get source) with
      | .failure => .failed
      | .success value => .value value

def weaken {Γ : VCtx Player L} {τ : L.Ty} {name : VarId} {binding : BindTy Player L} :
    GuardRead (R := R) Γ τ → GuardRead (R := R) ((name, binding) :: Γ) τ
  | .pending => .pending
  | .publicData source => .publicData (.there source)
  | .publication source => .publication (.there source)

@[simp] theorem get_weaken {Γ : VCtx Player L} {τ : L.Ty}
    {name : VarId} {binding : BindTy Player L} (read : GuardRead (R := R) Γ τ)
    (head : L.Val binding.base) (env : VEnv L Γ) :
    read.weaken.get (VEnv.cons (x := name) head env) = read.get env := by
  cases read <;> rfl

end GuardRead

/-- Source-independent retained guard code together with graph field reads. -/
structure GuardCheck (Γ : VCtx Player L) where
  subject : VarId
  payload : L.Ty
  code : DeferredGuardCode L subject payload
  subjectRead : GuardRead (R := R) Γ payload
  reads : ∀ {x τ}, HasVar code.schema x τ → GuardRead (R := R) Γ τ

namespace GuardCheck

def eval {Γ : VCtx Player L} (check : GuardCheck (R := R) Γ)
    (env : VEnv L Γ) : PublicationGuard.Verdict :=
  check.code.check (check.subjectRead.get env) fun h => (check.reads h).get env

end GuardCheck

/-- A typed projection from an ordinary expression schema to a public graph
field. The graph field may have a different identifier from the schema slot. -/
structure PublicRead (Γ : VCtx Player L) (τ : L.Ty) where
  field : VarId
  ref : HasVar Γ field (.pub τ)

/-- Ordinary expression code specialized to public immutable graph fields. -/
structure PublicExpr (Γ : VCtx Player L) (τ : L.Ty) where
  schema : Ctx L.Ty
  code : L.Expr schema τ
  reads : ∀ {x σ}, HasVar schema x σ → PublicRead (L := L) Γ σ

namespace PublicExpr

def eval {Γ : VCtx Player L} {τ : L.Ty} (expr : PublicExpr (L := L) Γ τ)
    (env : VEnv L Γ) : L.Val τ :=
  L.eval expr.code fun _ _ h => env.get (expr.reads h).ref

end PublicExpr

/-- Ordinary distribution code specialized to public immutable graph fields. -/
structure PublicDist (Γ : VCtx Player L) (τ : L.Ty) where
  schema : Ctx L.Ty
  code : L.DistExpr schema τ
  reads : ∀ {x σ}, HasVar schema x σ → PublicRead (L := L) Γ σ

namespace PublicDist

noncomputable def eval {Γ : VCtx Player L} {τ : L.Ty}
    (dist : PublicDist (L := L) Γ τ) (env : VEnv L Γ) :=
  L.evalDist dist.code fun _ _ h => env.get (dist.reads h).ref

end PublicDist

end Graph

/-- A canonical straight-line graph whose context is an immutable typed SSA
telescope. Resolve checks are specialized to the temporary proposed head. -/
inductive Graph (Player : Type) [DecidableEq Player] (L : IExpr)
    [R : IExpr.ResultTypes L] : VCtx Player L → VCtx Player L → Type where
  | ret {Γ} (payoffs : List (Player × Graph.PublicExpr (L := L) Γ L.int)) : Graph Player L Γ Γ
  | sample {Γ Δ} (name : VarId) {payload : L.Ty}
      (fresh : name ∉ Γ.map Prod.fst) (law : Graph.PublicDist (L := L) Γ payload)
      (next : Graph Player L ((name, .pub payload) :: Γ) Δ) : Graph Player L Γ Δ
  | bind {Γ Δ} (name : VarId) (owner : Player) {payload : L.Ty}
      (fresh : name ∉ Γ.map Prod.fst)
      (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ) :
      Graph Player L Γ Δ
  | resolve {Γ Δ} (outputName : VarId) (owner : Player) (bindingName : VarId)
      {payload : L.Ty} (fresh : outputName ∉ Γ.map Prod.fst)
      (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
      (checks : List (Graph.GuardCheck (R := inferInstance)
        ((outputName, .pub (R.result payload)) :: Γ)))
      (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ) :
      Graph Player L Γ Δ

end Vegas
