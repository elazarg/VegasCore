/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.Compiler
import Vegas.EventGraph.GuardValidation

/-! # Public validation of compiled source guards

The evaluator consumes only stored expression dependencies, although the
compiled strategy retains the complete declared source view. Public eligibility
and agreement on public graph fields imply exact agreement with the source
guard. The runtime must separately establish that agreement at the intended
decision context; this module does not equate a later defaulted context with
the context in which a commitment was chosen.
-/

namespace Vegas.ToEventGraph

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A publicly checkable compiled guard has exactly its source acceptance
predicate, even when the validator lacks private fields used only by the
player's choice policy. -/
theorem eventGuardOf_evalValidationStore?_eq_source
    {Γ : VCtx Player L} {actionName : VarId} {actionTy : L.Ty}
    (state : BuildState Player L Γ) (who : Player)
    (guard : L.Expr ((actionName, actionTy) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (G : Graph Player L) (hpublic : (eventGuardOf state who guard).PubliclyValidatable G)
    (action : L.Val actionTy) (fullStore publicStore : Store L)
    (available : ∀ {name bindTy} (binding : VHasVar Γ name bindTy),
      ∃ value, Store.getAs fullStore (state.fieldOf binding) bindTy.base = some value)
    (hagrees : ∀ ref, G.fieldRefPublic ref →
      Store.getAs publicStore ref.field ref.ty = Store.getAs fullStore ref.field ref.ty) :
    (eventGuardOf state who guard).evalValidationStore? action publicStore =
      some (evalGuard (Player := Player) (L := L) guard action
        ((sourceEnvOfStore state fullStore available).toView who).eraseEnv) := by
  obtain ⟨reads, hreads⟩ :=
    eventGuardOf_readEnv_of_sourceStoreAvailable state who guard fullStore available
  rw [(eventGuardOf state who guard).evalValidationStore?_eq_some_of_public
    G hpublic action reads fullStore publicStore hreads hagrees,
    eventGuardOf_eval_eq_eval,
    viewEnvOfReadEnv_eq_eraseEnv_sourceEnvOfStore state who fullStore available reads hreads]

end Vegas.ToEventGraph

/-- info: 'Vegas.ToEventGraph.eventGuardOf_evalValidationStore?_eq_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ToEventGraph.eventGuardOf_evalValidationStore?_eq_source
