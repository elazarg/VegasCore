/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventBindingInvariant
import Vegas.EventGraph.PrivateInputs

/-! # Private inputs have no commitment representation

The native semantic input environment supplies owner-visible ordinary values.
No executable event produces an input, no accepted commitment handle represents
one, and its initial candidate slot has no meaning. Public projections hide it.
-/

namespace Vegas.EventGraphRuntime.State

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Private inputs have no accepted handle in any state satisfying provenance. -/
theorem BindingInvariant.privateInput_no_handle {state : State graph}
    (invariant : state.BindingInvariant) (field : graph.Field) (owner : Player) (payload : L.Ty)
    (kind : graph.layout field = .privateInput owner payload) : state.accepted field = none := by
  cases accepted : state.accepted field with
  | none => rfl
  | some handle =>
      obtain ⟨_, binding⟩ := invariant.accepted_typed field handle accepted
      rw [kind] at binding
      cases binding

/-- Supplying a private input installs no candidate meaning for any principal. -/
theorem initial_privateInput_candidate (inputs : graph.Inputs) (input : graph.InputId)
    (owner who : Player) (payload : L.Ty)
    (kind : graph.inputLayout input = .privateInput owner payload) :
    (initial inputs).candidates.lookup (who, .initial input) = .fresh := by
  rw [initial_candidate]
  have empty (field : EventField Player L) (value : field.Value)
      (inputKind : field = .privateInput owner payload) :
      candidateOfValue who field value = .fresh := by
    cases inputKind
    rfl
  exact empty _ _ kind

end Vegas.EventGraphRuntime.State
