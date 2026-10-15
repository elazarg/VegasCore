/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventBindingInvariant

/-! # Reading accepted binding meanings from completed native fields -/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {state : State graph}

/-- An actual stored binding has exactly its accepted candidate's immutable
meaning. Absence of a handle is separate from an accepted candidate with a failed
meaning; both cases retain their original typed result. -/
theorem BindingInvariant.binding_value (valid : state.BindingInvariant)
    {owner : Player} {payload : L.Ty} (ref : FieldRef graph.layout (.binding owner payload))
    (value : PublicationResult (L.Val payload))
    (stored : ref.get? state.config.store = some value) :
    value = (state.accepted ref.field).elim .failure (fun candidate =>
      state.bindingResult candidate payload) := by
  cases accepted : state.accepted ref.field with
  | none =>
      simp only [Option.elim_none]
      cases value with
      | failure => rfl
      | success actual =>
          obtain ⟨candidate, associated, _owner, _fixed⟩ :=
            valid.success_provenance ref actual stored
          rw [accepted] at associated
          cases associated
  | some candidate =>
      simp only [Option.elim_some]
      cases result : state.bindingResult candidate payload with
      | failure =>
          cases value with
          | failure => rfl
          | success actual =>
              obtain ⟨other, associated, _owner, fixed⟩ :=
                valid.success_provenance ref actual stored
              have same : other = candidate := Option.some.inj (associated.symm.trans accepted)
              subst other
              have successful := (bindingResult_eq_success_iff state candidate payload actual).mpr
                fixed
              rw [result] at successful
              cases successful
      | success actual =>
          have fixed := (bindingResult_eq_success_iff state candidate payload actual).mp result
          have actualStored := valid.opening_stored ref candidate actual accepted fixed
          exact Option.some.inj (stored.symm.trans actualStored)

end Vegas.EventGraphRuntime.State
