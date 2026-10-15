/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.CompletedBindingReadback
import Vegas.EventGraph.ConfigRestriction

/-! # Recorded binding actions agree with surviving accepted meanings -/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {state : State graph}

private theorem binding_action_eq_value {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    {owner : Player} {payload : L.Ty} (binding : output = .binding owner payload)
    (code : EventCode layout output) (action : output.Action) (store : Store layout)
    (law : PMF output.Value) (value : output.Value)
    (evaluated : code.eval? action store = some law) (supported : value ∈ law.support) :
    cast (congrArg EventField.Action binding) action =
      cast (congrArg EventField.Value binding) value := by
  cases binding
  cases code
  change some (PMF.pure action) = some law at evaluated
  cases Option.some.inj evaluated
  exact ((PMF.mem_support_pure_iff _ _).mp supported).symm

/-- The actual retained action of a binding, including a failed typed result,
is the immutable meaning read from its accepted handle at the final native state. -/
theorem BindingInvariant.recorded_binding_action (valid : state.BindingInvariant)
    {inputs : graph.Inputs} (reachable : state.config.Reachable inputs)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) (recorded : ⟨event, action⟩ ∈ state.config.history) :
    cast (congrArg EventField.Action binding) action =
      (state.accepted (.inr event)).elim .failure (fun candidate =>
        state.bindingResult candidate payload) := by
  obtain ⟨law, value, stored, evaluated, supported⟩ :=
    reachable.history_output_semantics ⟨event, action⟩ recorded
  have same := binding_action_eq_value binding (graph.nodes event) action state.config.store law
    value evaluated supported
  let ref : FieldRef graph.layout (.binding owner payload) := ⟨.inr event, binding⟩
  have read : ref.get? state.config.store =
      some (cast (congrArg EventField.Value binding) value) := by
    change cast (congrArg (fun field => Option field.Value) binding)
      (state.config.outputs event) = _
    rw [stored]
    have castSome : ∀ {first second : EventField Player L} (equal : first = second)
        (value : first.Value), cast (congrArg (fun field => Option field.Value) equal)
          (some value) = some (cast (congrArg EventField.Value equal) value) := by
      intro first second equal value
      cases equal
      rfl
    exact castSome binding value
  exact same.trans (valid.binding_value ref _ read)

/-- Every completed binding has its actual original action in the retained
history, with exactly the final accepted meaning. No successful-value premise is needed. -/
theorem BindingInvariant.completed_binding_action (valid : state.BindingInvariant)
    {inputs : graph.Inputs} (reachable : state.config.Reachable inputs)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (completed : event ∈ state.config.cut.completed) :
    ∃ action : graph.Action event, ⟨event, action⟩ ∈ state.config.history ∧
      cast (congrArg EventField.Action binding) action =
        (state.accepted (.inr event)).elim .failure (fun candidate =>
          state.bindingResult candidate payload) := by
  obtain ⟨⟨actual, action⟩, recorded, same⟩ :=
    List.mem_map.mp ((state.config.history_exact event).mpr completed)
  change actual = event at same
  subst actual
  exact ⟨action, recorded, valid.recorded_binding_action reachable event owner payload binding
    action recorded⟩

end Vegas.EventGraphRuntime.State
