/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingOpaqueStep

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

/-- Actual phase handling installs the same next phase with the updated private
memory. Readiness keeps the new completion absent from the saved checkpoint;
the physical archive is empty on a clear initialized history. -/
theorem phase_handle_binding_memory (runtime : EventGraphRuntime graph)
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (state : PhaseRuntimeState graph) (clear : state.current.excluded = ∅)
    (archive : state.retired = []) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (message : Message Player (CommitAttemptPacket graph)) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (admitted : (message.payload.tokenValid state.attempt &&
      state.allows message.payload.packet.call &&
      !state.current.excludedCall message.payload.packet.call) = true)
    (sender : message.id.1 = owner) (candidateOwner : candidate.1 = owner)
    (ready : state.current.native.config.cut.Ready event)
    (timely : state.current.native.WithinDeadline runtime event)
    (vacant : state.current.native.accepted (.inr event) = none)
    (unused : state.current.native.HandleUnused candidate)
    (fixed : state.current.native.candidates.lookup candidate ≠ .fresh)
    (originalFixed : (memory.native owner state.current.native).candidates.lookup candidate ≠
      .fresh)
    (savedMissing : event ∉ state.entry.native.config.cut.completed) :
    let original := memory.native owner state.current.native
    let result := original.bindingResult candidate payload
    let remembered := memory.rememberCompletion event
      (cast (congrArg EventField.Action outputEq.symm) result)
      (cast (congrArg EventField.Value outputEq.symm) result)
    ∃ first second,
      ((memory.phased owner state).handle runtime message = some first) ∧
      (state.handle runtime message = some second) ∧
      remembered.OwnBindings owner ∧ remembered.phased owner second = first := by
  classical
  intro original result remembered
  obtain ⟨firstNative, secondNative, firstHandled, secondHandled, nextOwned, reconstructed⟩ :=
    handle_binding_memory runtime memory owner owned state.current.native event payload outputEq
      codeEq node message.id candidate sender candidateOwner ready timely vacant unused fixed
        originalFixed
  let firstRaw : PhaseRuntimeState graph :=
    { memory.phased owner state with current := ⟨firstNative, state.current.excluded⟩ }
  let secondRaw : PhaseRuntimeState graph :=
    { state with current := ⟨secondNative, state.current.excluded⟩ }
  have saved : remembered.native owner state.entry.native =
      memory.native owner state.entry.native :=
    rememberCompletion_native_pending memory owner state.entry.native event savedMissing _ _
  have raw : remembered.phased owner secondRaw = firstRaw := by
    dsimp only [firstRaw, secondRaw, phased, recovery]
    rw [saved, reconstructed, archive]
    rfl
  have otherAdmitted : (message.payload.tokenValid (memory.phased owner state).attempt &&
      (memory.phased owner state).allows message.payload.packet.call &&
      !(memory.phased owner state).current.excludedCall message.payload.packet.call) = true :=
    admitted
  refine ⟨firstRaw.normalize, secondRaw.normalize, ?_, ?_, nextOwned, ?_⟩
  · unfold PhaseRuntimeState.handle
    rw [otherAdmitted]
    simp only [↓reduceIte]
    change (handle runtime original ⟨message.id, message.payload.packet.call⟩).map _ = _
    rw [call, firstHandled]
    rfl
  · unfold PhaseRuntimeState.handle
    rw [admitted]
    simp only [↓reduceIte]
    rw [call, secondHandled]
    rfl
  · rw [← normalize_phased_of_clear remembered owner secondRaw clear, raw]

end Vegas.EventGraphRuntime.BindingShadow
