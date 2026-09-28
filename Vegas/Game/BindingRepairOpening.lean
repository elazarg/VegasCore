/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.BindingRepairPrefix
import Vegas.Pending.EventBindingInvariant

/-! # Successful bindings across the concrete source repair

Repair changes failed bindings only. Typed source/native agreement and actual
binding provenance therefore recover the same handle and authentic opening for
every originally successful binding, including another player's binding.
-/

noncomputable section

namespace Vegas.SourceProgram

open EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {Γ : SourceCtx Player L} {hidden : Player}
  {unpatch : ViewMap hidden Γ} {patched : PatchMap hidden Γ}
  {left right : Config Player L Γ}

omit [IExpr.ResultTypes L] in
/-- A successful original binding cannot be one of the repaired failures. -/
theorem Patched.success_kept
    (repair : Patched unpatch patched left.state right.state left.history right.history)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (ref : HasVar Γ name (.commitment owner payload)) (value : L.Val payload)
    (successful : left.state.get ref = .success value) :
    right.state.get ref = .success value := by
  by_cases own : owner = hidden
  · subst owner
    cases chosen : patched ref (right.view hidden) with
    | false => exact (repair.keptEq ref chosen).trans successful
    | true =>
        have impossible := (repair.replacedEq ref chosen).1
        rw [successful] at impossible
        cases impossible
  · exact (repair.foreignEq ref own).trans successful

/-- This is provenance of actual native candidates, not an inference from
opaque observations. No additional observer or independent private prior is
required. The graph may be the actual sequentialized service graph. -/
theorem repaired_success_provenance
    (repair : Patched unpatch patched left.state right.state left.history right.history)
    (refs : ContextRefs graph.layout Γ)
    (original repaired : EventGraphRuntime.State graph)
    (leftAgrees : refs.Agrees left.state original.config.store)
    (rightAgrees : refs.Agrees right.state repaired.config.store)
    (leftBinding : original.BindingInvariant) (rightBinding : repaired.BindingInvariant)
    (accepted : original.accepted = repaired.accepted)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (ref : HasVar Γ name (.commitment owner payload)) (value : L.Val payload)
    (successful : left.state.get ref = .success value) :
    (refs.get ref).get? original.config.store = some (.success value) ∧
    (refs.get ref).get? repaired.config.store = some (.success value) ∧
    ∃ handle,
      original.accepted (refs.get ref).field = some handle ∧
      repaired.accepted (refs.get ref).field = some handle ∧ handle.1 = owner ∧
      original.candidates.lookup handle = .openable ⟨payload, value⟩ ∧
      repaired.candidates.lookup handle = .openable ⟨payload, value⟩ := by
  have leftStored := leftAgrees ref
  have rightStored := rightAgrees ref
  rw [successful] at leftStored
  rw [repair.success_kept ref value successful] at rightStored
  obtain ⟨handle, associated, owned, fixed⟩ :=
    leftBinding.success_provenance (refs.get ref) value leftStored
  obtain ⟨other, associated', _, fixed'⟩ :=
    rightBinding.success_provenance (refs.get ref) value rightStored
  have same : handle = other := Option.some.inj
    (associated.symm.trans ((congrFun accepted (refs.get ref).field).trans associated'))
  subst other
  exact ⟨leftStored, rightStored, handle, associated, associated', owned, fixed, fixed'⟩

end Vegas.SourceProgram
