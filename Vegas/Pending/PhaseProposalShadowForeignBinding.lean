/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.PhaseProposalShadowProgress

/-! # Actual other-owner binding handlers through general phase recovery -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A foreign binding retains its exact private result. The actual handlers
are constructed before the general normalizer selects its next logical mask;
no clear state or empty retired archive is needed. -/
theorem PhaseStateFrame.handle_foreign_binding {memory : BindingShadow graph} {hidden : Player}
    {original repaired : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory hidden original repaired)
    (owned : memory.OwnBindings hidden)
    (supported : memory.CompletedAt repaired.current.native.config)
    (runtime : EventGraphRuntime graph) (actor : Player) (different : actor ≠ hidden)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind actor payload)
    (node : nodeView graph event = .bind actor payload outputEq codeEq)
    (message : Message Player (CommitAttemptPacket graph)) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (admitted : (message.payload.tokenValid repaired.attempt &&
      repaired.allows message.payload.packet.call &&
      !repaired.current.excludedCall message.payload.packet.call) = true)
    (sender : message.id.1 = actor) (candidateOwner : candidate.1 = actor)
    (ready : repaired.current.native.config.cut.Ready event)
    (timely : repaired.current.native.WithinDeadline runtime event)
    (vacant : repaired.current.native.accepted (.inr event) = none)
    (unused : repaired.current.native.HandleUnused candidate)
    (fixed : repaired.current.native.candidates.lookup candidate ≠ .fresh) :
    ∃ (next : BindingShadow graph) (first second : PhaseRuntimeState graph),
      original.handle runtime message = some first ∧
      repaired.handle runtime message = some second ∧
      next.OwnBindings hidden ∧ next.candidates = memory.candidates ∧
      PhaseStateFrame next hidden first second ∧
      next.CompletedAt second.current.native.config ∧
      (original.entry.native.config.store.BindingRefines repaired.entry.native.config.store →
        original.current.native.config.store.BindingRefines repaired.current.native.config.store →
        first.entry.native.config.store.BindingRefines second.entry.native.config.store ∧
        first.current.native.config.store.BindingRefines second.current.native.config.store) := by
  classical
  obtain ⟨firstNative, secondNative, firstHandled, secondHandled, reconstructed⟩ :=
    handle_foreign_binding_memory runtime memory hidden owned repaired.current.native actor
      different event payload outputEq codeEq node message.id candidate sender candidateOwner
        ready timely vacant unused fixed
  have nextSupport : memory.CompletedAt secondNative.config := by
    intro prior present
    exact handle_completed_subset runtime repaired.current.native secondNative
      ⟨message.id, .commitment event candidate⟩ secondHandled (supported prior present)
  let firstRaw : PhaseRuntimeState graph :=
    { original with current := ⟨firstNative, original.current.excluded⟩ }
  let secondRaw : PhaseRuntimeState graph :=
    { repaired with current := ⟨secondNative, repaired.current.excluded⟩ }
  have excludedEq : original.current.excluded = repaired.current.excluded := by
    rw [frame.current]
    rfl
  have rawFrame : PhaseStateFrame memory hidden firstRaw secondRaw := by
    refine ⟨frame.phases, frame.generation, frame.entry, ?_, frame.retired⟩
    exact congrArg₂ RecoveryState.mk reconstructed.symm excludedEq
  obtain ⟨next, nextOwned, candidates, paired, nextSupported, refineStores⟩ :=
    rawFrame.normalize owned nextSupport
  have rawRefinement
      (preserved : original.current.native.config.store.BindingRefines
        repaired.current.native.config.store) :
      firstRaw.current.native.config.store.BindingRefines
        secondRaw.current.native.config.store := by
    have nativeEq : original.current.native = memory.native hidden repaired.current.native := by
      rw [frame.current]
      rfl
    rw [nativeEq] at preserved
    have progressed := supported.completionStep_refinement hidden preserved
      (completionStep_handle runtime repaired.current.native secondNative
        ⟨message.id, .commitment event candidate⟩ secondHandled)
    change firstNative.config.store.BindingRefines secondNative.config.store
    rw [← reconstructed]
    exact progressed
  have attempts : original.attempt = repaired.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have allows : original.allows message.payload.packet.call =
      repaired.allows message.payload.packet.call := by
    simp only [PhaseRuntimeState.allows, frame.phases]
  have excluded : original.current.excludedCall message.payload.packet.call =
      repaired.current.excludedCall message.payload.packet.call := by rw [frame.current]; rfl
  have firstAdmitted : (message.payload.tokenValid original.attempt &&
      original.allows message.payload.packet.call &&
      !original.current.excludedCall message.payload.packet.call) = true := by
    rw [attempts, allows, excluded]
    exact admitted
  refine ⟨next, firstRaw.normalize, secondRaw.normalize, ?_, ?_, nextOwned, candidates,
    paired, nextSupported, ?_⟩
  · unfold PhaseRuntimeState.handle
    rw [firstAdmitted]
    simp only [↓reduceIte]
    rw [frame.current]
    change (handle runtime (memory.native hidden repaired.current.native)
      ⟨message.id, message.payload.packet.call⟩).map _ = _
    rw [call, firstHandled]
    simp only [Option.map_some, RecoveryState.inclusionResult, firstRaw, frame.current, recovery]
  · unfold PhaseRuntimeState.handle
    rw [admitted]
    simp only [↓reduceIte]
    rw [call, secondHandled]
    rfl
  · intro entryRef currentRef
    exact refineStores entryRef (rawRefinement currentRef)

/-- The accepting original foreign packet supplies its actual native
conditions. Its fixed meaning is identical outside the designated owner's
catalogue, so the target handler and dynamic normalization are constructed. -/
theorem PhaseStateFrame.repair_foreign_binding {memory : BindingShadow graph} {hidden : Player}
    {original repaired : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory hidden original repaired)
    (owned : memory.OwnBindings hidden)
    (supported : memory.CompletedAt repaired.current.native.config)
    (runtime : EventGraphRuntime graph) (actor : Player) (different : actor ≠ hidden)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (message : Message Player (CommitAttemptPacket graph)) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (fixed : original.current.native.candidates.lookup candidate ≠ .fresh)
    (next : PhaseRuntimeState graph)
    (accepted : original.handle runtime message = some next) :
    ∃ (nextMemory : BindingShadow graph) (image : PhaseRuntimeState graph),
      repaired.handle runtime message = some image ∧
      nextMemory.OwnBindings hidden ∧ nextMemory.candidates = memory.candidates ∧
      PhaseStateFrame nextMemory hidden next image ∧
      nextMemory.CompletedAt image.current.native.config ∧
      (original.entry.native.config.store.BindingRefines repaired.entry.native.config.store →
        original.current.native.config.store.BindingRefines repaired.current.native.config.store →
        next.entry.native.config.store.BindingRefines image.entry.native.config.store ∧
        next.current.native.config.store.BindingRefines image.current.native.config.store) := by
  classical
  have admitted : (message.payload.tokenValid original.attempt &&
      original.allows message.payload.packet.call &&
      !original.current.excludedCall message.payload.packet.call) = true := by
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · assumption
    · cases accepted
  have nativeAccepted : ∃ native, handle runtime original.current.native
      ⟨message.id, .commitment event candidate⟩ = some native := by
    unfold PhaseRuntimeState.handle at accepted
    rw [admitted] at accepted
    simp only [↓reduceIte, call, Option.map_eq_some_iff] at accepted
    obtain ⟨native, handled, _⟩ := accepted
    exact ⟨native, handled⟩
  obtain ⟨native, handled⟩ := nativeAccepted
  obtain ⟨ready, timely, actualActor, actualPayload, actualOutput, codeEq, node, sender,
      candidateOwner, vacant, unused, _⟩ :=
    (handle_commitment_iff runtime original.current.native native message.id event candidate).mp
      handled
  obtain ⟨sameActor, samePayload⟩ := EventField.binding.inj (actualOutput.symm.trans outputEq)
  subst sameActor
  subst samePayload
  let actor := actualActor
  let payload := actualPayload
  have rightReady : repaired.current.native.config.cut.Ready event := by
    rw [frame.current] at ready
    exact ready
  have rightTimely : repaired.current.native.WithinDeadline runtime event := by
    rw [frame.current] at timely
    exact timely
  have rightVacant : repaired.current.native.accepted (.inr event) = none := by
    rw [frame.current] at vacant
    exact vacant
  have rightUnused : repaired.current.native.HandleUnused candidate := by
    rw [frame.current] at unused
    exact unused
  have rightFixed : repaired.current.native.candidates.lookup candidate ≠ .fresh := by
    have same : candidate = (actor, candidate.2) := Prod.ext candidateOwner rfl
    rw [same, frame.current] at fixed
    simp only [recovery, BindingShadow.native, CommitmentCandidates.lookup] at fixed
    have distinct : actor ≠ hidden := different
    rw [ite_eq_right distinct] at fixed
    rw [same]
    exact fixed
  have attempts : original.attempt = repaired.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have allows : original.allows message.payload.packet.call =
      repaired.allows message.payload.packet.call := by
    simp only [PhaseRuntimeState.allows, frame.phases]
  have excluded : original.current.excludedCall message.payload.packet.call =
      repaired.current.excludedCall message.payload.packet.call := by rw [frame.current]; rfl
  have rightAdmitted : (message.payload.tokenValid repaired.attempt &&
      repaired.allows message.payload.packet.call &&
      !repaired.current.excludedCall message.payload.packet.call) = true := by
    rwa [attempts, allows, excluded] at admitted
  obtain ⟨nextMemory, first, image, firstHandled, imageHandled, nextOwned, candidates,
      paired, nextSupport, refinement⟩ :=
    frame.handle_foreign_binding owned supported runtime actor different event payload outputEq
      codeEq node message candidate call rightAdmitted sender candidateOwner rightReady rightTimely
        rightVacant rightUnused rightFixed
  have sameFirst : first = next := Option.some.inj (firstHandled.symm.trans accepted)
  subst first
  exact ⟨nextMemory, image, imageHandled, nextOwned, candidates, paired, nextSupport, refinement⟩

end Vegas.EventGraphRuntime.BindingShadow
