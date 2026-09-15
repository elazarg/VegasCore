/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Basic

/-! # Guard validation from expression dependencies

The player's choice footprint and the validator's read footprint have different
roles. A choice may depend on the owner's full declared information, while
checking its guard needs only the stored dependencies of the retained guard
expression. The proposed action is supplied separately, not read from storage.

This module defines an executable dependency-local evaluator and proves its
agreement with the graph guard. It does not establish that a guard's reads are
publicly available at opening time or that timeout defaults remain legal.
-/

namespace Vegas.EventGraph

variable {L : IExpr}

private def storedReadRefs {Γ : Ctx L.Ty}
    (fieldOf : {name : VarId} → {ty : L.Ty} → HasVar Γ name ty → Nat)
    (names : Finset VarId) : Finset (FieldRef L) :=
  match Γ with
  | [] => ∅
  | (name, ty) :: _ =>
      let rest := storedReadRefs (fun binding => fieldOf (.there binding)) names
      if name ∈ names then insert ⟨fieldOf .here, ty⟩ rest else rest

private theorem storedReadRefs_mem {Γ : Ctx L.Ty} {name : VarId} {ty : L.Ty}
    (binding : HasVar Γ name ty)
    (fieldOf : {name : VarId} → {ty : L.Ty} → HasVar Γ name ty → Nat)
    (names : Finset VarId) (hname : name ∈ names) :
    (⟨fieldOf binding, ty⟩ : FieldRef L) ∈ storedReadRefs fieldOf names := by
  induction binding with
  | here => simp [storedReadRefs, hname]
  | there binding ih =>
      simp only [storedReadRefs]
      split
      · exact Finset.mem_insert_of_mem (ih (fun binding => fieldOf (.there binding)) hname)
      · exact ih (fun binding => fieldOf (.there binding)) hname

private theorem storedReadRefs_forall {Γ : Ctx L.Ty}
    (fieldOf : {name : VarId} → {ty : L.Ty} → HasVar Γ name ty → Nat)
    (names : Finset VarId) (property : FieldRef L → Prop)
    (hall : ∀ {name ty} (binding : HasVar Γ name ty),
      name ∈ names → property ⟨fieldOf binding, ty⟩) :
    ∀ ref ∈ storedReadRefs fieldOf names, property ref := by
  induction Γ with
  | nil => simp [storedReadRefs]
  | cons head tail ih =>
      rcases head with ⟨name, ty⟩
      simp only [storedReadRefs]
      split
      · intro ref href
        rcases Finset.mem_insert.mp href with rfl | href
        · exact hall .here (by assumption)
        · exact ih (fun binding => fieldOf (.there binding))
            (fun binding => hall (.there binding)) ref href
      · exact ih (fun binding => fieldOf (.there binding))
          (fun binding => hall (.there binding))

namespace EventGuard

/-- Stored bindings whose names occur in the expression language's declared
dependency set. This is a sound static footprint, not a semantic minimality
claim. Unused private choice information need not be available to a validator. -/
def validationReads (guard : EventGuard L) : Finset (FieldRef L) :=
  storedReadRefs guard.code.fieldOf (L.exprDeps guard.code.expr)

theorem validation_read_mem (guard : EventGuard L) {name : VarId} {ty : L.Ty}
    (binding : HasVar guard.code.Context name ty)
    (hname : name ∈ L.exprDeps guard.code.expr) :
    guard.code.ref binding ∈ guard.validationReads :=
  storedReadRefs_mem binding guard.code.fieldOf _ hname

theorem validationReads_subset (guard : EventGuard L) :
    guard.validationReads ⊆ guard.choiceReads :=
  storedReadRefs_forall guard.code.fieldOf _ _ (fun binding _ => guard.read_mem binding)

/-- Evaluate the retained guard from the action and its stored dependencies.
No lookup is made for a stored binding outside `validationReads`. -/
def evalValidation (guard : EventGuard L) (action : L.Val guard.ty)
    (env : ReadEnv L guard.validationReads) : Bool :=
  L.toBool <| L.evalDeps guard.code.expr fun _ _ binding dependency =>
    match binding with
    | .here => action
    | .there stored => env.read (guard.code.ref stored)
        (guard.validation_read_mem stored dependency)

/-- Dependency-local validation agrees with the ordinary graph guard on the
restriction of any legal choice-information environment. -/
theorem evalValidation_eq_eval (guard : EventGuard L) (action : L.Val guard.ty)
    (env : ReadEnv L guard.choiceReads) :
    guard.evalValidation action
      ⟨fun ref href => env.read ref (guard.validationReads_subset href)⟩ =
      guard.eval action env := by
  unfold evalValidation eval
  congr 1
  rw [← L.evalDeps_eq_eval]
  congr 1
  funext name ty binding dependency
  cases binding <;> rfl

/-- Validate from runtime storage, rejecting unavailable or ill-typed stored
dependencies. A Boolean `false` is a successfully evaluated, rejecting guard. -/
def evalValidationStore? (guard : EventGuard L) (action : L.Val guard.ty)
    (store : Store L) : Option Bool :=
  (ReadEnv.ofStoreExec? store guard.validationReads).map (guard.evalValidation action)

/-- A store agreeing with the player's view on guard dependencies evaluates
the same guard; it need not contain the rest of the player's information. -/
theorem evalValidationStore?_eq_some (guard : EventGuard L) (action : L.Val guard.ty)
    (env : ReadEnv L guard.choiceReads) (store : Store L)
    (hagrees : ∀ ref (href : ref ∈ guard.validationReads),
      Store.getAs store ref.field ref.ty =
        some (env.read ref (guard.validationReads_subset href))) :
    guard.evalValidationStore? action store = some (guard.eval action env) := by
  have available : ∀ ref, ref ∈ guard.validationReads →
      (Store.getAs store ref.field ref.ty).isSome := by
    intro ref href
    rw [hagrees ref href]
    rfl
  have heq : ReadEnv.ofStoreChecked store guard.validationReads available =
      (⟨fun ref href => env.read ref (guard.validationReads_subset href)⟩ :
        ReadEnv L guard.validationReads) := by
    apply ReadEnv.ext
    intro ref href
    exact Option.some.inj
      ((ReadEnv.getAs_ofStoreChecked store guard.validationReads available href).symm.trans
        (hagrees ref href))
  simp only [evalValidationStore?, ReadEnv.ofStoreExec?, dif_pos available, Option.map_some,
    heq, evalValidation_eq_eval]

/-- The guard can be checked from public graph storage if each of its stored
dependencies is public. The player's larger choice footprint remains intact. -/
def PubliclyValidatable {Player : Type} [DecidableEq Player]
    (guard : EventGuard L) (G : Graph Player L) : Prop :=
  ∀ ref ∈ guard.validationReads, G.fieldRefPublic ref

/-- Public stored dependencies suffice; bindings unused by the guard
may remain private, even though they are part of the player's choice view. -/
theorem publiclyValidatable_of_dependencies
    {Player : Type} [DecidableEq Player] (guard : EventGuard L) (G : Graph Player L)
    (hpublic : ∀ {name ty} (binding : HasVar guard.code.Context name ty),
      name ∈ L.exprDeps guard.code.expr → G.fieldRefPublic (guard.code.ref binding)) :
    guard.PubliclyValidatable G :=
  storedReadRefs_forall guard.code.fieldOf _ _ hpublic

/-- Public eligibility and public-store agreement suffice for validation.
This makes the static predicate an actual premise of the evaluator theorem. -/
theorem evalValidationStore?_eq_some_of_public
    {Player : Type} [DecidableEq Player] (guard : EventGuard L) (G : Graph Player L)
    (hpublic : guard.PubliclyValidatable G) (action : L.Val guard.ty)
    (env : ReadEnv L guard.choiceReads) (fullStore publicStore : Store L)
    (henv : ReadEnv.ofStore? fullStore guard.choiceReads = some env)
    (hagrees : ∀ ref, G.fieldRefPublic ref →
      Store.getAs publicStore ref.field ref.ty = Store.getAs fullStore ref.field ref.ty) :
    guard.evalValidationStore? action publicStore = some (guard.eval action env) := by
  apply guard.evalValidationStore?_eq_some action env publicStore
  intro ref href
  rw [hagrees ref (hpublic ref href)]
  exact ReadEnv.ofStore?_read henv (guard.validationReads_subset href)

end EventGuard

end Vegas.EventGraph

/-- info: 'Vegas.EventGraph.EventGuard.evalValidationStore?_eq_some_of_public'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.EventGuard.evalValidationStore?_eq_some_of_public
