/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingClockReplay

/-! # Raw response aliases retain their exact original private recall -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Operational normalization does not discard the original own action.
The actual packet and application effect agree, while private reconstruction
records the supplied raw alias rather than its normal form. -/
theorem response_alias (frame : Frame runtime leaks memory owner original repaired)
    (shadow : BindingShadow graph) (canonical raw target : WitnessedSubmission graph)
    (application : (runtime.reactiveApplication leaks).submit original.application owner canonical =
      (runtime.reactiveApplication leaks).submit original.application owner raw)
    (packet : canonical.emit
        ((runtime.reactiveApplication leaks).submit original.application owner canonical) owner
          (original.network.known owner) =
      raw.emit ((runtime.reactiveApplication leaks).submit original.application owner raw) owner
        (original.network.known owner))
    (calls : canonical.call.packet = raw.call.packet)
    (paired : Frame runtime leaks
      ⟨shadow, memory.responses ++ [(memory.shadow.inputView runtime leaks
        (repaired.observe (runtime.reactiveApplication leaks) owner), ⟨some canonical⟩)]⟩
      owner (original.respond (runtime.reactiveApplication leaks) owner ⟨some canonical⟩)
        (repaired.respond (runtime.reactiveApplication leaks) owner ⟨some target⟩)) :
    Frame runtime leaks
      ⟨shadow, memory.responses ++ [(memory.shadow.inputView runtime leaks
        (repaired.observe (runtime.reactiveApplication leaks) owner), ⟨some raw⟩)]⟩
      owner (original.respond (runtime.reactiveApplication leaks) owner ⟨some raw⟩)
        (repaired.respond (runtime.reactiveApplication leaks) owner ⟨some target⟩) := by
  let app := runtime.reactiveApplication leaks
  have networks : (original.respond app owner ⟨some canonical⟩).network =
      (original.respond app owner ⟨some raw⟩).network := by
    change (original.network.submit owner _).2 = (original.network.submit owner _).2
    exact congrArg (fun emitted => (original.network.submit owner emitted).2) packet
  have observation : (original.respond app owner ⟨some canonical⟩).observe app owner =
      (original.respond app owner ⟨some raw⟩).observe app owner := by
    change (⟨(original.respond app owner ⟨some canonical⟩).network.observe owner,
      app.observePlayer (app.submit original.application owner canonical) owner,
      original.receipts⟩ : app.PlayerView) =
        ⟨(original.respond app owner ⟨some raw⟩).network.observe owner,
          app.observePlayer (app.submit original.application owner raw) owner, original.receipts⟩
    rw [networks, application]
  have targetPacket : raw.emit (app.submit original.application owner raw) owner
      (original.network.known owner) =
      target.emit (app.submit repaired.application owner target) owner
        (repaired.network.known owner) := by
    have histories := congrArg MessageNetwork.inputs paired.network
    change original.network.inputs ++ [_] = repaired.network.inputs ++ [_] at histories
    have sameInputs := congrArg MessageNetwork.inputs frame.network
    rw [sameInputs] at histories
    have emitted := congrArg Message.payload
      (List.singleton_injective (List.append_cancel_left histories))
    exact packet.symm.trans emitted
  refine ⟨?_, paired.observed.trans observation, ?_, networks.symm.trans paired.network,
    paired.service, ?_, ?_, ?_, ?_, ?_⟩
  · exact memory.restoreRecall_submit runtime leaks original repaired owner raw target
      frame.lengths frame.past frame.observed frame.network targetPacket
  · simpa only [List.length_append, List.length_singleton] using paired.lengths
  · intro who different
    change (app.submit original.application owner raw).playerView who = _
    rw [← application]
    exact paired.views who different
  · intro who different
    rw [app.respond_recall_other original owner who different,
      app.respond_recall_other repaired owner who different]
    exact frame.recall who different
  · intro query
    change (app.submit original.application owner raw).candidates.lookup _ = .fresh ↔ _
    rw [← application]
    exact paired.slots query
  · change (app.submit original.application owner raw).config.store.BindingRefines _
    rw [← application]
    exact paired.successful
  · have submitted := paired.submissions
    rw [runtime.submissionRecall_respond, runtime.submissionRecall_respond] at submitted ⊢
    have same : runtime.submittedEvent? leaks (⟨some canonical⟩ : app.Action) =
        runtime.submittedEvent? leaks (⟨some raw⟩ : app.Action) := by
      change canonical.call.packet.event? graph = raw.call.packet.event? graph
      rw [calls]
    rwa [same] at submitted

end Vegas.EventGraphRuntime.BindingMemory.Frame


namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Every permitted raw binding alias is repaired at its original fresh slot.
The permanent emitted packet is unchanged, and the private memory retains the
original evidence request, including a request whose actual result was absent. -/
theorem raw_binding_response (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (left : PhaseCount.CountRecall runtime leaks original)
    (right : PhaseCount.CountRecall runtime leaks repaired)
    (stored : repaired.application.StoredCheckpoint)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (fresh : original.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh)
    (ready : original.application.current.native.config.cut.Ready event)
    (bounded : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (original.recall owner) (original.observe (phaseApplication runtime leaks) owner)) :
    let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
    let canonical : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let source : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩
    let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
      | none => some (⟨payload, L.someValue payload⟩ : Raw L)
      | some _ => opening
    let target : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacementOpening⟩, .none⟩⟩
    let view := (execution runtime leaks repaired).observe nativeApp owner
    let change := memory.repairResponse runtime (nativeLeaks (graph := graph)) owner view
      (action runtime leaks canonical)
    let remembered : BindingMemory runtime (nativeLeaks (graph := graph)) :=
      ⟨change.2, memory.responses ++
        [(memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view,
          action runtime leaks source)]⟩
    target ∈ PhaseCount.onePacketActions runtime leaks bounds owner (repaired.recall owner)
        (repaired.observe (phaseApplication runtime leaks) owner) ∧
      Frame runtime leaks remembered owner
        (original.respond (phaseApplication runtime leaks) owner source)
        (repaired.respond (phaseApplication runtime leaks) owner target) := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let call : Submission graph := ⟨.commitment event (owner, .prepared serial), opening⟩
  let canonicalMaterial : WitnessedSubmission graph := ⟨call, .none⟩
  let rawMaterial : WitnessedSubmission graph := ⟨call, evidence⟩
  let canonical : app.Action := ⟨some canonicalMaterial⟩
  let source : app.Action := ⟨some rawMaterial⟩
  let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
    | none => some (⟨payload, L.someValue payload⟩ : Raw L)
    | some _ => opening
  let targetMaterial : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), replacementOpening⟩, .none⟩
  let target : app.Action := ⟨some targetMaterial⟩
  let view := (execution runtime leaks repaired).observe nativeApp owner
  let change := memory.repairResponse runtime (nativeLeaks (graph := graph)) owner view
    (action runtime leaks canonical)
  let remembered : BindingMemory runtime (nativeLeaks (graph := graph)) :=
    ⟨change.2, memory.responses ++
      [(memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view,
        action runtime leaks source)]⟩
  have permitted : PhaseCount.permits (app.outputs (original.recall owner))
      (PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
        (original.observe app owner) rawMaterial) = true := by
    have allowed := member
    rw [PhaseCount.mem_onePacketActions] at allowed
    rcases allowed.2 with impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have normalized : (PhaseCount.normalization runtime leaks).action owner (original.recall owner)
      (original.observe app owner) source = canonical := by
    have absent := PhaseCount.normalize_binding_evidence_none runtime leaks owner
      (original.recall owner) (original.observe app owner) rawMaterial event
        (owner, .prepared serial) rfl permitted
    have effective : openingEffective owner (original.observe app owner).application.1
        (.commitment event (owner, .prepared serial)) := ⟨rfl, fresh⟩
    have calls : ((PhaseCount.normalization runtime leaks).normalize owner
        (original.observe app owner).application
        (ReactiveApplication.ResponseMenu.knownPackets (original.recall owner)
          (original.observe app owner)) rawMaterial).call = call :=
      Submission.normalizeReactive_effective _ _ _ effective
    exact congrArg (fun material => (⟨some material⟩ : app.Action))
      (congrArg₂ WitnessedSubmission.mk calls absent)
  have canonicalMember := PhaseCount.normalize_mem_onePacketActions runtime leaks bounds owner
    (original.recall owner) (original.observe app owner) source member
  rw [normalized] at canonicalMember
  have effects := (PhaseCount.normalization runtime leaks).effects original owner source left.1
  rw [normalized] at effects
  have paired := frame.binding_response bounds left right stored event payload outputEq codeEq
    node serial opening fresh ready bounded canonicalMember
  change target ∈ _ ∧ Frame runtime leaks
    ⟨change.2, memory.responses ++
      [(memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view,
        action runtime leaks canonical)]⟩ owner
      (original.respond app owner canonical) (repaired.respond app owner target) at paired
  refine ⟨paired.1, ?_⟩
  have nativeCanonical := paired.2.live
  rw [execution_respond_of_onePacket runtime leaks bounds original owner canonical canonicalMember,
    execution_respond_of_onePacket runtime leaks bounds repaired owner target paired.1]
      at nativeCanonical
  have nativeNetworks :
      ((execution runtime leaks original).respond nativeApp owner
        (action runtime leaks canonical)).network =
      ((execution runtime leaks original).respond nativeApp owner
        (action runtime leaks source)).network := by
    rw [← execution_respond_of_onePacket runtime leaks bounds original owner canonical
      canonicalMember, ← execution_respond_of_onePacket runtime leaks bounds original owner
        source member]
    exact congrArg PhaseBindingRepair.network effects.2.1
  have nativePackets : canonicalMaterial.emit
      (nativeApp.submit original.application.current.native owner canonicalMaterial) owner
        ((execution runtime leaks original).network.known owner) =
      rawMaterial.emit (nativeApp.submit original.application.current.native owner rawMaterial)
        owner
        ((execution runtime leaks original).network.known owner) := by
    have histories := congrArg MessageNetwork.inputs nativeNetworks
    change (execution runtime leaks original).network.inputs ++ [_] =
      (execution runtime leaks original).network.inputs ++ [_] at histories
    exact congrArg Message.payload (List.singleton_injective (List.append_cancel_left histories))
  have native := BindingMemory.Frame.response_alias frame.live change.2 canonicalMaterial
    rawMaterial targetMaterial rfl nativePackets rfl nativeCanonical
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
      (execution runtime leaks (original.respond app owner source))
      (execution runtime leaks (repaired.respond app owner target)) := by
    rw [execution_respond_of_onePacket runtime leaks bounds original owner source member,
      execution_respond_of_onePacket runtime leaks bounds repaired owner target paired.1]
    exact native
  have savedSource : (checkpoint runtime leaks (original.respond app owner canonical)).application =
      (checkpoint runtime leaks (original.respond app owner source)).application :=
    congrArg (fun state : PhaseRuntimeState graph =>
      { state.entry.native with candidates := state.current.native.candidates }) effects.1
  have saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
      (checkpoint runtime leaks (original.respond app owner source))
      (checkpoint runtime leaks (repaired.respond app owner target)) := by
    apply checkpointFrame live
      (checkpoint runtime leaks (original.respond app owner source)).application
      (checkpoint runtime leaks (repaired.respond app owner target)).application
    · rw [← savedSource]
      exact congrArg ReactiveApplication.PlayerView.application paired.2.saved.observed
    · rw [← savedSource]
      exact paired.2.saved.views
    · rw [← savedSource]
      exact paired.2.saved.slots
    · rw [← savedSource]
      exact paired.2.saved.successful
  refine ⟨live, saved, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
    frame.archiveOriginal, frame.archiveRepaired, effects.2.1.symm.trans paired.2.network,
      frame.service, ?_⟩
  intro who different
  rw [app.respond_recall_other original owner who different,
    app.respond_recall_other repaired owner who different]
  exact frame.foreignRecall who different

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
