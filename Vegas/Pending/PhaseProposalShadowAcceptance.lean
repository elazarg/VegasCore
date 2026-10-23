/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.PhaseProposalSubmittedBindings

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
      next.CompletedAt second.current.native.config ∧
      (original.entry.native.config.store.BindingRefines repaired.entry.native.config.store →
        original.current.native.config.store.BindingRefines repaired.current.native.config.store →
        PreparedBindingResult original.current.native repaired.current.native candidate payload →
        first.entry.native.config.store.BindingRefines second.entry.native.config.store ∧
        first.current.native.config.store.BindingRefines second.current.native.config.store) := by
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
  let targetResult := repaired.current.native.bindingResult candidate payload
  let targetAction := cast (congrArg EventField.Action outputEq.symm) targetResult
  let targetValue := cast (congrArg EventField.Value outputEq.symm) targetResult
  have firstConfig : firstNative.config =
      (memory.native owner repaired.current.native).config.complete event ready oldAction
        oldValue := by
    have actual := handle_commitment_eq runtime (memory.native owner repaired.current.native)
      message.id event candidate owner payload outputEq codeEq node ready timely sender
        candidateOwner vacant unused
    exact congrArg State.config (Option.some.inj (firstHandled.symm.trans actual))
  have secondConfig : secondNative.config =
      repaired.current.native.config.complete event ready targetAction targetValue := by
    have actual := handle_commitment_eq runtime repaired.current.native message.id event candidate
      owner payload outputEq codeEq node ready timely sender candidateOwner vacant unused
    exact congrArg State.config (Option.some.inj (secondHandled.symm.trans actual))
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
  obtain ⟨next, nextOwned, candidates, normalized, normalizedSupport, refineStores⟩ :=
    rawFrame.normalize nextOwned nextSupport
  have rawRefinement
      (preserved : original.current.native.config.store.BindingRefines
        repaired.current.native.config.store)
      (prepared : PreparedBindingResult original.current.native repaired.current.native
        candidate payload) :
      firstRaw.current.native.config.store.BindingRefines
        secondRaw.current.native.config.store := by
    have nativeEq : original.current.native = memory.native owner repaired.current.native := by
      rw [frame.current]
      rfl
    rw [nativeEq] at preserved
    change firstNative.config.store.BindingRefines secondNative.config.store
    rw [firstConfig, secondConfig]
    apply Config.bindingRefines_complete preserved event ready ready oldAction targetAction
      oldValue targetValue
    apply EventField.BindingRefines.cast_some outputEq.symm
    intro value successful
    have originalResult : original.current.native.bindingResult candidate payload =
        .success value := by
      rw [nativeEq]
      exact Option.some.inj successful
    exact congrArg some (prepared.2.2.2 value originalResult)
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
    candidates, normalized, normalizedSupport, ?_⟩
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
  · intro entryRef currentRef prepared
    exact refineStores entryRef (rawRefinement currentRef prepared)

end Vegas.EventGraphRuntime.BindingShadow
