/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.PhaseBindingForeignMemory

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
      next.CompletedAt second.current.native.config := by
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
  obtain ⟨next, nextOwned, candidates, paired, nextSupported⟩ :=
    rawFrame.normalize owned nextSupport
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
    paired, nextSupported⟩
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

end Vegas.EventGraphRuntime.BindingShadow
