/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingOpaqueStep
import Vegas.Pending.PhaseBindingRepairInclusion
import Vegas.Pending.PhaseBindingShadow
import Vegas.Pending.ReactiveBindingShadow
import Vegas.Pending.ReactiveBindingShadowInvariant

/-! # Remembering actual all-value binding completions across phase installation -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Both actual native handlers accept, and the remembered original action and
result reconstruct the complete successor, including a typed failure. -/
theorem handle_binding_memory (runtime : EventGraphRuntime graph)
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (state : State graph) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph)
    (sender : id.1 = owner) (candidateOwner : candidate.1 = owner)
    (ready : state.config.cut.Ready event) (timely : state.WithinDeadline runtime event)
    (vacant : state.accepted (.inr event) = none) (unused : state.HandleUnused candidate)
    (fixed : state.candidates.lookup candidate ≠ .fresh)
    (originalFixed : (memory.native owner state).candidates.lookup candidate ≠ .fresh) :
    let original := memory.native owner state
    let result := original.bindingResult candidate payload
    let remembered := memory.rememberCompletion event
      (cast (congrArg EventField.Action outputEq.symm) result)
      (cast (congrArg EventField.Value outputEq.symm) result)
    ∃ first second,
      handle runtime original ⟨id, .commitment event candidate⟩ = some first ∧
      handle runtime state ⟨id, .commitment event candidate⟩ = some second ∧
      remembered.OwnBindings owner ∧ remembered.native owner second = first := by
  classical
  intro original result remembered
  have originalReady : original.config.cut.Ready event := ready
  have originalTimely : original.WithinDeadline runtime event := timely
  have originalVacant : original.accepted (.inr event) = none := vacant
  have originalUnused : original.HandleUnused candidate := unused
  let action (current : State graph) : graph.Action event :=
    cast (congrArg EventField.Action outputEq.symm) (current.bindingResult candidate payload)
  let value (current : State graph) : (graph.outputLayout event).Value :=
    cast (congrArg EventField.Value outputEq.symm) (current.bindingResult candidate payload)
  let first : State graph :=
    { original.complete event originalReady (action original) (value original) with
      accepted := Function.update original.accepted (.inr event) (some candidate) }
  let second : State graph :=
    { state.complete event ready (action state) (value state) with
      accepted := Function.update state.accepted (.inr event) (some candidate) }
  refine ⟨first, second, ?_, ?_, owned.rememberCompletion event payload outputEq _ _, ?_⟩
  · rw [handle_commitment_eq runtime original id event candidate owner payload outputEq codeEq
      node originalReady originalTimely sender candidateOwner originalVacant originalUnused,
      original.candidates.freeze_eq_self_of_not_fresh candidate originalFixed]
    rfl
  · rw [handle_commitment_eq runtime state id event candidate owner payload outputEq codeEq
      node ready timely sender candidateOwner vacant unused,
      state.candidates.freeze_eq_self_of_not_fresh candidate fixed]
    rfl
  · dsimp only [first, second, remembered, result, action, value]
    rw [native_setAccepted, rememberCompletion_native_complete]
    rfl

end Vegas.EventGraphRuntime.BindingShadow
