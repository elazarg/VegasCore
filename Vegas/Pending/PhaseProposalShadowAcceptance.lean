/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.PhaseBindingCompletionMemory

/-! # Actual accepted bindings followed by general recovery normalization

The native handler determines the hidden old result. Its existing completion
reconstruction is combined with the actual dynamically masked normalizer,
including retries and nonempty permanent exclusion sets.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Count-preserving admission at an actual owned binding, with the saved
absence and native acceptance conditions supplied by their owning provenance
lemmas. No normalized image, successor memory or clear attempt is assumed. -/
theorem PhaseStateFrame.handle_binding {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph} (frame : PhaseStateFrame memory owner
      original repaired) (owned : memory.OwnBindings owner)
    (supported : memory.CompletedAt repaired.current.native.config)
    (runtime : EventGraphRuntime graph) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (message : Message Player (CommitAttemptPacket graph)) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (admitted : (message.payload.tokenValid repaired.attempt &&
      repaired.allows message.payload.packet.call &&
      !repaired.current.excludedCall message.payload.packet.call) = true)
    (sender : message.id.1 = owner) (candidateOwner : candidate.1 = owner)
    (ready : repaired.current.native.config.cut.Ready event)
    (timely : repaired.current.native.WithinDeadline runtime event)
    (vacant : repaired.current.native.accepted (.inr event) = none)
    (unused : repaired.current.native.HandleUnused candidate)
    (fixed : repaired.current.native.candidates.lookup candidate ≠ .fresh)
    (originalFixed : (memory.native owner repaired.current.native).candidates.lookup
      candidate ≠ .fresh)
    (savedMissing : event ∉ repaired.entry.native.config.cut.completed) :
    ∃ (next : BindingShadow graph) (first second : PhaseRuntimeState graph),
      original.handle runtime message = some first ∧
      repaired.handle runtime message = some second ∧
      next.OwnBindings owner ∧ next.candidates = memory.candidates ∧
      PhaseStateFrame next owner first second ∧
      next.CompletedAt second.current.native.config := by
  classical
  let result := (memory.native owner repaired.current.native).bindingResult candidate payload
  let oldAction := cast (congrArg EventField.Action outputEq.symm) result
  let oldValue := cast (congrArg EventField.Value outputEq.symm) result
  let remembered := memory.rememberCompletion event oldAction oldValue
  obtain ⟨firstNative, secondNative, firstHandled, secondHandled, nextOwned, reconstructed⟩ :=
    handle_binding_memory runtime memory owner owned repaired.current.native event payload
      outputEq codeEq node message.id candidate sender candidateOwner ready timely vacant unused
      fixed originalFixed
  have sameRemembered : remembered.native owner secondNative = firstNative := reconstructed
  have nextCompleted : event ∈ secondNative.config.cut.completed := by
    obtain ⟨named, addressed, _, completed⟩ := handle_completes runtime
      repaired.current.native secondNative ⟨message.id, .commitment event candidate⟩ secondHandled
    have namedEq : named = event := Option.some.inj addressed.symm
    exact namedEq ▸ completed
  have nextSupport : remembered.CompletedAt secondNative.config := by
    intro prior present
    by_cases same : prior = event
    · exact same ▸ nextCompleted
    · apply handle_completed_subset runtime repaired.current.native secondNative
        ⟨message.id, .commitment event candidate⟩ secondHandled
      apply supported prior
      simpa only [remembered, rememberCompletion, Function.update_of_ne same,
        Function.update_of_ne (Sum.inr_injective.ne same)] using present
  let firstRaw : PhaseRuntimeState graph :=
    { original with current := ⟨firstNative, original.current.excluded⟩ }
  let secondRaw : PhaseRuntimeState graph :=
    { repaired with current := ⟨secondNative, repaired.current.excluded⟩ }
  have rawFrame : PhaseStateFrame remembered owner firstRaw secondRaw := by
    refine ⟨frame.phases, frame.generation, ?_, ?_, frame.retired⟩
    · exact frame.entry.trans
        (rememberCompletion_saved memory owner repaired.entry event savedMissing oldAction
          oldValue).symm
    · change (⟨firstNative, original.current.excluded⟩ : RecoveryState graph) =
        ⟨remembered.native owner secondNative, repaired.current.excluded⟩
      rw [sameRemembered, frame.current]
      rfl
  obtain ⟨next, nextOwned, candidates, normalized, normalizedSupport⟩ :=
    rawFrame.normalize nextOwned nextSupport
  have attempts : original.attempt = repaired.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have allows : original.allows message.payload.packet.call =
      repaired.allows message.payload.packet.call := by
    simp only [PhaseRuntimeState.allows, frame.phases]
  have excluded : original.current.excludedCall message.payload.packet.call =
      repaired.current.excludedCall message.payload.packet.call := by
    rw [frame.current]
    rfl
  have originalAdmitted : (message.payload.tokenValid original.attempt &&
      original.allows message.payload.packet.call &&
      !original.current.excludedCall message.payload.packet.call) = true := by
    rw [attempts, allows, excluded]
    exact admitted
  refine ⟨next, firstRaw.normalize, secondRaw.normalize, ?_, ?_, nextOwned,
    candidates, normalized, normalizedSupport⟩
  · unfold PhaseRuntimeState.handle
    rw [originalAdmitted]
    simp only [↓reduceIte]
    rw [frame.current]
    change (handle runtime (memory.native owner repaired.current.native)
      ⟨message.id, message.payload.packet.call⟩).map _ = _
    rw [call, firstHandled]
    simp only [Option.map_some, RecoveryState.inclusionResult, firstRaw, frame.current, recovery]
  · unfold PhaseRuntimeState.handle
    rw [admitted]
    simp only [↓reduceIte]
    rw [call, secondHandled]
    rfl

end Vegas.EventGraphRuntime.BindingShadow
