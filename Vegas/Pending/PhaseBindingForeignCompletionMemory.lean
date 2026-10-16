/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingForeignMemory

/-! # Actual foreign binding handlers through phase normalization -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A foreign binding completes with the same physical candidate on both sides.
Its actual normalized phase outcomes retain the existing all-value memory,
without adding a foreign entry to that owner's private memory. -/
theorem phase_handle_foreign_binding_memory (runtime : EventGraphRuntime graph)
    (memory : BindingShadow graph) (hidden : Player) (owned : memory.OwnBindings hidden)
    (state : PhaseRuntimeState graph) (clear : state.current.excluded = ∅)
    (owner : Player) (different : owner ≠ hidden) (event : graph.EventId) (payload : L.Ty)
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
    (fixed : state.current.native.candidates.lookup candidate ≠ .fresh) :
    ∃ first second,
      (memory.phased hidden state).handle runtime message = some first ∧
      state.handle runtime message = some second ∧
      memory.phased hidden second = first := by
  classical
  obtain ⟨firstNative, secondNative, firstHandled, secondHandled, reconstructed⟩ :=
    handle_foreign_binding_memory runtime memory hidden owned state.current.native owner different
      event payload outputEq codeEq node message.id candidate sender candidateOwner ready timely
        vacant unused fixed
  let firstRaw : PhaseRuntimeState graph :=
    { memory.phased hidden state with current := ⟨firstNative, state.current.excluded⟩ }
  let secondRaw : PhaseRuntimeState graph :=
    { state with current := ⟨secondNative, state.current.excluded⟩ }
  have raw : memory.phased hidden secondRaw = firstRaw := by
    dsimp only [firstRaw, secondRaw, phased, recovery]
    rw [reconstructed]
  have otherAdmitted : (message.payload.tokenValid (memory.phased hidden state).attempt &&
      (memory.phased hidden state).allows message.payload.packet.call &&
      !(memory.phased hidden state).current.excludedCall message.payload.packet.call) = true :=
    admitted
  refine ⟨firstRaw.normalize, secondRaw.normalize, ?_, ?_, ?_⟩
  · unfold PhaseRuntimeState.handle
    rw [otherAdmitted]
    simp only [↓reduceIte]
    change (handle runtime (memory.native hidden state.current.native)
      ⟨message.id, message.payload.packet.call⟩).map _ = _
    rw [call, firstHandled]
    rfl
  · unfold PhaseRuntimeState.handle
    rw [admitted]
    simp only [↓reduceIte]
    rw [call, secondHandled]
    rfl
  · rw [← normalize_phased_of_clear memory hidden secondRaw clear, raw]

end Vegas.EventGraphRuntime.BindingShadow
