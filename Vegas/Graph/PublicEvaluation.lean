/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.Semantics

/-! # Public-only evaluation for typed immutable graphs

The evaluators in this file expose the concrete input required by a native
graph runtime.  They can inspect public bindings, but have no operation for
reading a sealed binding.  Resolution receives its proposed publication from
the caller and evaluates the retained checks after adding that proposal as a
temporary public head.
-/

noncomputable section
namespace Vegas.Graph

open Interaction

variable {Player : Type} {L : IExpr}

/-- Values of precisely the public bindings in a graph context. -/
def PublicValues (Γ : VCtx Player L) : Type :=
  ∀ {field τ}, HasVar Γ field (.pub τ) → L.Val τ

namespace PublicValues

/-- Project the public portion of a full graph environment. -/
def ofVEnv {Γ : VCtx Player L} (env : VEnv L Γ) : PublicValues Γ :=
  fun source => env.get source

/-- Add a public value at the head of the graph context. -/
def consPublic {Γ : VCtx Player L} {name : VarId} {τ : L.Ty}
    (value : L.Val τ) (values : PublicValues (Player := Player) Γ) :
    PublicValues ((name, .pub τ) :: Γ) :=
  fun source =>
    match source with
    | .here => value
    | .there source => values source

/-- Extend public values across a sealed head.  No sealed value is supplied. -/
def consSealed {Γ : VCtx Player L} {name : VarId} {owner : Player} {τ : L.Ty}
    (values : PublicValues (L := L) Γ) :
    PublicValues ((name, .sealed owner τ) :: Γ) :=
  fun source =>
    match source with
    | .there source => values source

@[simp] theorem ofVEnv_cons_public {Γ : VCtx Player L} {name : VarId} {τ : L.Ty}
    (value : L.Val τ) (env : VEnv L Γ) :
    (ofVEnv (VEnv.cons (x := name) (τ := .pub τ) value env) :
      PublicValues ((name, .pub τ) :: Γ)) =
    (consPublic (name := name) value (ofVEnv env) :
      PublicValues ((name, .pub τ) :: Γ)) := by
  funext field σ source
  cases source <;> rfl

@[simp] theorem ofVEnv_cons_sealed {Γ : VCtx Player L} {name : VarId}
    {owner : Player} {τ : L.Ty} (value : L.Val τ) (env : VEnv L Γ) :
    (ofVEnv (VEnv.cons (x := name) (τ := .sealed owner τ) value env) :
      PublicValues ((name, .sealed owner τ) :: Γ)) =
    (consSealed (name := name) (owner := owner) (τ := τ) (ofVEnv env) :
      PublicValues ((name, .sealed owner τ) :: Γ)) := by
  funext field σ source
  cases source with
  | there source => rfl

end PublicValues

namespace PublicExpr

/-- Evaluate public expression code from public values alone. -/
def evalPublic {Γ : VCtx Player L} {τ : L.Ty} (expr : PublicExpr (L := L) Γ τ)
    (values : PublicValues Γ) : L.Val τ :=
  L.eval expr.code fun _ _ h => values (expr.reads h).ref

theorem evalPublic_ofVEnv {Γ : VCtx Player L} {τ : L.Ty}
    (expr : PublicExpr (L := L) Γ τ) (env : VEnv L Γ) :
    expr.evalPublic (PublicValues.ofVEnv env) = expr.eval env := by
  rfl

end PublicExpr

namespace PublicDist

/-- Evaluate public distribution code from public values alone. -/
noncomputable def evalPublic {Γ : VCtx Player L} {τ : L.Ty}
    (dist : PublicDist (L := L) Γ τ) (values : PublicValues Γ) :=
  L.evalDist dist.code fun _ _ h => values (dist.reads h).ref

theorem evalPublic_ofVEnv {Γ : VCtx Player L} {τ : L.Ty}
    (dist : PublicDist (L := L) Γ τ) (env : VEnv L Γ) :
    dist.evalPublic (PublicValues.ofVEnv env) = dist.eval env := by
  rfl

end PublicDist

variable [R : IExpr.ResultTypes L]

namespace GuardRead

/-- Resolve a retained guard read from public values alone. -/
def getPublic {Γ : VCtx Player L} {τ : L.Ty} :
    GuardRead (R := R) Γ τ → PublicValues Γ → Publication (L.Val τ)
  | .pending, _ => .pending
  | .publicData source, values => .value (values source)
  | .publication source, values =>
      match R.valueEquiv _ (values source) with
      | .failure => .failed
      | .success value => .value value

theorem getPublic_ofVEnv {Γ : VCtx Player L} {τ : L.Ty}
    (read : GuardRead (R := R) Γ τ) (env : VEnv L Γ) :
    read.getPublic (PublicValues.ofVEnv env) = read.get env := by
  cases read <;> rfl

end GuardRead

namespace GuardCheck

/-- Evaluate a retained guard from public values alone. -/
def evalPublic {Γ : VCtx Player L} (check : GuardCheck (R := R) Γ)
    (values : PublicValues Γ) : PublicationGuard.Verdict :=
  check.code.check (check.subjectRead.getPublic values) fun h =>
    (check.reads h).getPublic values

theorem evalPublic_ofVEnv {Γ : VCtx Player L} (check : GuardCheck (R := R) Γ)
    (env : VEnv L Γ) :
    check.evalPublic (PublicValues.ofVEnv env) = check.eval env := by
  unfold evalPublic GuardCheck.eval
  rw [GuardRead.getPublic_ofVEnv]
  apply DeferredGuardCode.check_congr <;> simp [GuardRead.getPublic_ofVEnv]

end GuardCheck

/-- Decide a list of retained checks using public values alone. -/
def checksAcceptedPublic {Γ : VCtx Player L}
    (checks : List (GuardCheck (R := R) Γ)) (values : PublicValues Γ) : Bool :=
  checks.all fun check => check.evalPublic values != .rejected

theorem checksAcceptedPublic_ofVEnv {Γ : VCtx Player L}
    (checks : List (GuardCheck (R := R) Γ)) (env : VEnv L Γ) :
    checksAcceptedPublic checks (PublicValues.ofVEnv env) = checksAccepted checks env := by
  induction checks with
  | nil => rfl
  | cons check checks ih =>
      change
        ((check.evalPublic (PublicValues.ofVEnv env) != .rejected) &&
            checksAcceptedPublic checks (PublicValues.ofVEnv env)) =
          ((check.eval env != .rejected) && checksAccepted checks env)
      rw [GuardCheck.evalPublic_ofVEnv, ih]

/-- Resolve a supplied proposal using only the old public values and the
temporary public result inspected by the retained checks. -/
def acceptedProposal {Γ : VCtx Player L} {payload : L.Ty} {outputName : VarId}
    (checks : List (GuardCheck (R := R) ((outputName, .pub (R.result payload)) :: Γ)))
    (values : PublicValues Γ) (proposal : PublicationResult (L.Val payload)) :
    PublicationResult (L.Val payload) :=
  let tentative : PublicValues ((outputName, .pub (R.result payload)) :: Γ) :=
    PublicValues.consPublic ((R.valueEquiv _).symm proposal) values
  if checksAcceptedPublic checks tentative then proposal else .failure

theorem acceptedProposal_eq_acceptedResult {Γ : VCtx Player L} {owner : Player}
    {payload : L.Ty} {outputName bindingName : VarId}
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R) ((outputName, .pub (R.result payload)) :: Γ)))
    (env : VEnv L Γ) (disclose : Bool) :
    acceptedProposal checks (PublicValues.ofVEnv env)
        (proposedResult source env disclose) =
      acceptedResult source checks env disclose := by
  unfold acceptedProposal acceptedResult
  dsimp only
  rw [← PublicValues.ofVEnv_cons_public, checksAcceptedPublic_ofVEnv]

end Vegas.Graph
