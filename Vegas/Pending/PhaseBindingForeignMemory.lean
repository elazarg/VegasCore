/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingMemoryFreshness

/-! # Actual foreign binding completions outside the private memory -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A real unmodified completion commutes with the existing private memory.
Both the exact dependent action and its stored value are retained. -/
theorem config_complete_unmodified (memory : BindingShadow graph) (state : graph.Config)
    (event : graph.EventId) (ready : state.cut.Ready event)
    (noValue : memory.values (.inr event) = none) (noAction : memory.actions event = none)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    memory.config (state.complete event ready action value) =
      (memory.config state).complete event ready action value := by
  classical
  apply Config.ext_fields (left := memory.config (state.complete event ready action value))
    (right := (memory.config state).complete event ready action value) rfl rfl
  · funext query
    by_cases same : query = event
    · subst query
      simp only [config, Config.complete, Function.update_self, Option.map_some,
        noValue, Option.getD_none]
    · simp only [config, Config.complete, Function.update_of_ne same]
  · change (state.history ++ [(⟨event, action⟩ : graph.Completion)]).map memory.completion =
      state.history.map memory.completion ++ [(⟨event, action⟩ : graph.Completion)]
    rw [List.map_append]
    simp only [List.map_cons, List.map_nil, completion, noAction, Option.getD_none]

variable [DecidableEq Player]

/-- The native completion includes the original readiness timestamps and all
physical admission tables; it does not use a successful-store refinement. -/
theorem native_complete_unmodified (memory : BindingShadow graph) (owner : Player)
    (state : State graph) (event : graph.EventId) (ready : state.config.cut.Ready event)
    (noValue : memory.values (.inr event) = none) (noAction : memory.actions event = none)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    memory.native owner (state.complete event ready action value) =
      (memory.native owner state).complete event ready action value := by
  change (⟨memory.config (state.config.complete event ready action value), state.accepted,
      (memory.native owner state).candidates, state.clock,
      State.refreshActivated (state.config.complete event ready action value) state.clock
        state.activatedAt⟩ : State graph) = _
  rw [config_complete_unmodified memory state.config event ready noValue noAction action value]
  rfl

/-- Actual accepting handlers for a foreign binding preserve the SAME memory.
The foreign candidate may encode failure or any typed value. -/
theorem handle_foreign_binding_memory (runtime : EventGraphRuntime graph)
    (memory : BindingShadow graph) (hidden : Player) (owned : memory.OwnBindings hidden)
    (state : State graph) (owner : Player) (different : owner ≠ hidden)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph)
    (sender : id.1 = owner) (candidateOwner : candidate.1 = owner)
    (ready : state.config.cut.Ready event) (timely : state.WithinDeadline runtime event)
    (vacant : state.accepted (.inr event) = none) (unused : state.HandleUnused candidate)
    (fixed : state.candidates.lookup candidate ≠ .fresh) :
    ∃ first second,
      handle runtime (memory.native hidden state) ⟨id, .commitment event candidate⟩ = some first ∧
      handle runtime state ⟨id, .commitment event candidate⟩ = some second ∧
      memory.native hidden second = first := by
  classical
  have acting : graph.actor? event = some owner :=
    (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
      (congrArg EventCode.actor codeEq)
  have visible : graph.fieldVisibleTo owner (.inr event) := by
    change (graph.outputLayout event).VisibleTo owner
    rw [outputEq]
    rfl
  have noValue := owned.foreign_value_none owner different (.inr event) visible
  have noAction := owned.foreign_action_none owner different event acting
  have candidateEq : (memory.native hidden state).candidates.lookup candidate =
      state.candidates.lookup candidate := by
    simp only [native, CommitmentCandidates.lookup, candidateOwner, different, ↓reduceIte]
  have originalFixed : (memory.native hidden state).candidates.lookup candidate ≠ .fresh :=
    candidateEq ▸ fixed
  have resultEq : (memory.native hidden state).bindingResult candidate payload =
      state.bindingResult candidate payload := by
    simp only [State.bindingResult, candidateEq]
  let action (current : State graph) : graph.Action event :=
    cast (congrArg EventField.Action outputEq.symm) (current.bindingResult candidate payload)
  let value (current : State graph) : (graph.outputLayout event).Value :=
    cast (congrArg EventField.Value outputEq.symm) (current.bindingResult candidate payload)
  let original := memory.native hidden state
  let first : State graph :=
    { original.complete event ready (action original) (value original) with
      accepted := Function.update original.accepted (.inr event) (some candidate) }
  let second : State graph :=
    { state.complete event ready (action state) (value state) with
      accepted := Function.update state.accepted (.inr event) (some candidate) }
  refine ⟨first, second, ?_, ?_, ?_⟩
  · rw [handle_commitment_eq runtime (memory.native hidden state) id event candidate owner payload
      outputEq codeEq node ready timely sender candidateOwner vacant unused,
      (memory.native hidden state).candidates.freeze_eq_self_of_not_fresh candidate originalFixed]
    rfl
  · rw [handle_commitment_eq runtime state id event candidate owner payload outputEq codeEq node
      ready timely sender candidateOwner vacant unused,
      state.candidates.freeze_eq_self_of_not_fresh candidate fixed]
    rfl
  · dsimp only [first, second]
    rw [native_setAccepted, native_complete_unmodified memory hidden state event ready noValue
      noAction (action state) (value state)]
    dsimp only [action, value, original]
    rw [resultEq]
    rfl

end Vegas.EventGraphRuntime.BindingShadow
