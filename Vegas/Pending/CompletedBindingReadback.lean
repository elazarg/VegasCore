/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventBindingReadback

/-! # Total typed readback of completed binding cells -/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {state : State graph}

/-- Completion supplies the cell, and actual binding provenance supplies its
typed value even for an absent or unusable accepted handle. -/
theorem BindingInvariant.binding_read (valid : state.BindingInvariant)
    {owner : Player} {payload : L.Ty} (ref : FieldRef graph.layout (.binding owner payload))
    (event : graph.EventId) (field : ref.field = .inr event)
    (completed : event ∈ state.config.cut.completed) :
    ref.get? state.config.store = some ((state.accepted ref.field).elim .failure
      (fun candidate => state.bindingResult candidate payload)) := by
  have available : (state.config.store ref.field).isSome = true := by
    rw [field]
    change (state.config.outputs event).isSome = true
    exact (state.config.output_available event).mpr completed
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (ref.get?_isSome _ available)
  rw [valid.binding_value ref value stored] at stored
  exact stored

end Vegas.EventGraphRuntime.State
