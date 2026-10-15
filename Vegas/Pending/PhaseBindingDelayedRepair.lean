/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRawInclusion
import Vegas.Pending.ReactiveBindingSubmissionFrame

/-! # Delayed physical binding inclusion transports saved and live repair frames -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

namespace Frame

theorem admission (frame : Frame runtime leaks memory owner original repaired)
    (message : Message Player (CommitAttemptPacket graph)) :
    (message.payload.tokenValid original.application.attempt &&
      original.application.allows message.payload.packet.call &&
      !original.application.current.excludedCall message.payload.packet.call) =
    (message.payload.tokenValid repaired.application.attempt &&
      repaired.application.allows message.payload.packet.call &&
      !repaired.application.current.excludedCall message.payload.packet.call) := by
  simp only [PhaseRuntimeState.attempt, PhaseRuntimeState.allows, RecoveryState.excludedCall,
    RecoveryState.excludedEvent, frame.phases, frame.generation, frame.clearOriginal,
    frame.clearRepaired]

/-- The delayed opaque packet is included under the same physical identifier.
Native repair supplies the raw edge; clean phase installation also updates the
saved checkpoint, so an older still-private repaired binding remains paired. -/
theorem binding_inclusion (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph)
    (sender : id.1 = owner) (owned : candidate.1 = owner)
    (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (packet : PhaseCount.nativeMessage message =
      ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩)
    (admitted : (message.payload.tokenValid original.application.attempt &&
      original.application.allows message.payload.packet.call &&
      !original.application.current.excludedCall message.payload.packet.call) = true)
    (ready : original.application.current.native.config.cut.Ready event)
    (timely : original.application.current.native.WithinDeadline runtime event)
    (vacant : original.application.current.native.accepted (.inr event) = none)
    (unused : original.application.current.native.HandleUnused candidate)
    (leftFixed : original.application.current.native.candidates.lookup candidate ≠ .fresh)
    (rightFixed : repaired.application.current.native.candidates.lookup candidate ≠ .fresh)
    (rememberedAction : memory.shadow.actions event = some
      (cast (congrArg EventField.Action outputEq.symm)
        (original.application.current.native.bindingResult candidate payload)))
    (rememberedValue : memory.shadow.values (.inr event) = some
      (cast (congrArg EventField.Value outputEq.symm)
        (original.application.current.native.bindingResult candidate payload)))
    (successful : ∀ value,
      original.application.current.native.bindingResult candidate payload = .success value →
        repaired.application.current.native.bindingResult candidate payload = .success value) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  have leftFound : (execution runtime leaks original).network.lookup id =
      some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩ := by
    change (PhaseBindingRepair.network original.network).lookup id = _
    rw [network_lookup, found, Option.map_some, packet]
  have rightPhysicalFound : repaired.network.lookup id = some message := frame.network ▸ found
  have rightFound : (execution runtime leaks repaired).network.lookup id =
      some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩ := by
    rw [← frame.live.network]
    exact leftFound
  have call : message.payload.packet.call = .commitment event candidate :=
    congrArg (fun value : Message Player (WitnessedPacket graph) => value.payload.call) packet
  have native := frame.live.pending_binding_inclusion event payload outputEq codeEq node id
    candidate sender owned leftFound ready timely vacant unused leftFixed rightFixed
    rememberedAction rememberedValue successful
  let left := rawBindingInclude runtime leaks original id
  let right := rawBindingInclude runtime leaks repaired id
  let leftRecorded : app.Execution := { left with environmentRecall :=
    original.environmentRecall ++ [⟨original.observeEnvironment app, .include id⟩] }
  let rightRecorded : app.Execution := { right with environmentRecall :=
    repaired.environmentRecall ++ [⟨repaired.observeEnvironment app, .include id⟩] }
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (execution runtime leaks leftRecorded) (execution runtime leaks rightRecorded) := by
    change BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      { execution runtime leaks left with environmentRecall := _ }
      { execution runtime leaks right with environmentRecall := _ }
    rw [show execution runtime leaks left = _ from execution_rawBindingInclude runtime leaks
      original id, show execution runtime leaks right = _ from
        execution_rawBindingInclude runtime leaks repaired id]
    dsimp only at native
    rw [PhaseBindingRepair.observeEnvironment runtime leaks original,
      PhaseBindingRepair.observeEnvironment runtime leaks repaired] at native
    simpa only [leftRecorded, rightRecorded, List.map_append, List.map_cons, List.map_nil,
      environmentEntry, command, execution, app] using native
  have leftCandidates := runtime.reactive_include_fixed_binding_candidates
    (nativeLeaks (graph := graph)) (execution runtime leaks original) id event candidate none
      leftFound leftFixed
  have rightCandidates := runtime.reactive_include_fixed_binding_candidates
    (nativeLeaks (graph := graph)) (execution runtime leaks repaired) id event candidate none
      rightFound rightFixed
  have leftCheckpoint : checkpoint runtime leaks leftRecorded =
      { execution runtime leaks leftRecorded with application :=
        (checkpoint runtime leaks original).application } := by
    have stateEq : ({ original.application.entry.native with candidates :=
        ((execution runtime leaks original).includePending nativeApp id).application.candidates } :
          State graph) = (checkpoint runtime leaks original).application := by
      rw [leftCandidates]
      rfl
    exact congrArg (fun state : State graph => (⟨state,
      (execution runtime leaks leftRecorded).network,
      (execution runtime leaks leftRecorded).receipts,
      (execution runtime leaks leftRecorded).recall,
      (execution runtime leaks leftRecorded).environmentRecall⟩ : nativeApp.Execution)) stateEq
  have rightCheckpoint : checkpoint runtime leaks rightRecorded =
      { execution runtime leaks rightRecorded with application :=
        (checkpoint runtime leaks repaired).application } := by
    have stateEq : ({ repaired.application.entry.native with candidates :=
        ((execution runtime leaks repaired).includePending nativeApp id).application.candidates } :
          State graph) = (checkpoint runtime leaks repaired).application := by
      rw [rightCandidates]
      rfl
    exact congrArg (fun state : State graph => (⟨state,
      (execution runtime leaks rightRecorded).network,
      (execution runtime leaks rightRecorded).receipts,
      (execution runtime leaks rightRecorded).recall,
      (execution runtime leaks rightRecorded).environmentRecall⟩ : nativeApp.Execution)) stateEq
  have saved := checkpointFrame live (checkpoint runtime leaks original).application
    (checkpoint runtime leaks repaired).application
    (congrArg ReactiveApplication.PlayerView.application frame.saved.observed)
    frame.saved.views frame.saved.slots frame.saved.successful
  rw [← leftCheckpoint, ← rightCheckpoint] at saved
  have raw : Frame runtime leaks memory owner leftRecorded rightRecorded := by
    refine ⟨live, saved, frame.phases, frame.generation, frame.clearOriginal,
      frame.clearRepaired, frame.archiveOriginal, frame.archiveRepaired, ?_, ?_,
      frame.foreignRecall⟩
    · exact congrArg (fun pool => (pool.includePending id).2) frame.network
    · change original.environmentRecall ++ [⟨original.observeEnvironment app, .include id⟩] =
        repaired.environmentRecall ++ [⟨repaired.observeEnvironment app, .include id⟩]
      rw [frame.service, frame.environment_input]
  have publicNative : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  have rightReady : repaired.application.current.native.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← publicNative, State.publicView_eventReady]
    exact ready
  have rightTimely : repaired.application.current.native.WithinDeadline runtime event := by
    have clocks : original.application.current.native.clock =
        repaired.application.current.native.clock := congrArg PublicView.clock publicNative
    have stamps : original.application.current.native.activatedAt =
        repaired.application.current.native.activatedAt :=
      congrArg PublicView.activatedAt publicNative
    unfold State.WithinDeadline at timely ⊢
    rw [← clocks, ← stamps]
    exact timely
  have associated : original.application.current.native.accepted =
      repaired.application.current.native.accepted := congrArg PublicView.accepted publicNative
  have rightVacant : repaired.application.current.native.accepted (.inr event) = none := by
    rw [← associated]; exact vacant
  have rightUnused : repaired.application.current.native.HandleUnused candidate := by
    intro field accepted
    exact unused field ((congrFun associated field).trans accepted)
  have leftHandled := runtime.handle_commitment_eq original.application.current.native id event
    candidate owner payload outputEq codeEq node ready timely sender owned vacant unused
  have rightHandled := runtime.handle_commitment_eq repaired.application.current.native id event
    candidate owner payload outputEq codeEq node rightReady rightTimely sender owned rightVacant
      rightUnused
  have messageId : message.id = id := congrArg Message.id packet
  have leftActual := include_binding_eq_normalize runtime leaks original id message found event
    candidate call admitted _ (by simpa only [messageId, call] using leftHandled)
  have rightActual := include_binding_eq_normalize runtime leaks repaired id message
    rightPhysicalFound event candidate call ((frame.admission message) ▸ admitted) _
      (by simpa only [messageId, call] using rightHandled)
  rw [leftActual, rightActual]
  exact raw.normalize

end Frame
end Vegas.EventGraphRuntime.PhaseBindingRepair
