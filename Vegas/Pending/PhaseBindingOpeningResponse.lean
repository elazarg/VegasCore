/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingInertResponse

/-! # Actual counted opening responses during directed private binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A legal opening reads the same surviving typed binding in the image.
Its original evidence and unused raw preparation are replayed exactly; actual
certificate/count history supplies the binding provenance at the callback. -/
theorem opening_response (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, original⟩))
    (right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, repaired⟩))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (preparation : Option (Raw L)) (evidence : EvidenceRequest graph)
    (member : (⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (original.recall owner) (original.observe (phaseApplication runtime leaks) owner))
    (request : original.application.SeedRequest owner ⟨original.application.attempt, event⟩)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq) :
    let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
    let response : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩
    let remembered := memory.record runtime (nativeLeaks (graph := graph))
      (memory.shadow.inputView runtime (nativeLeaks (graph := graph))
        ((execution runtime leaks repaired).observe nativeApp owner))
      (action runtime leaks response)
    response ∈ PhaseCount.onePacketActions runtime leaks bounds owner (repaired.recall owner)
        (repaired.observe (phaseApplication runtime leaks) owner) ∧
      Frame runtime leaks remembered owner
        (original.respond (phaseApplication runtime leaks) owner response)
        (repaired.respond (phaseApplication runtime leaks) owner response) := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let material : WitnessedSubmission graph :=
    ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩
  let response : app.Action := ⟨some material⟩
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler left
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler right
  have countLeft := PhaseCount.countRecall_history runtime leaks rawLeft
  have countRight := PhaseCount.countRecall_history runtime leaks rawRight
  have leftBinding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawLeft
  have rightBinding := phaseBindingRecord_history runtime leaks plan inputs horizon
    scheduler rawRight
  obtain ⟨value, typed, successful, accepted, _fixed⟩ :=
    opening_response_binding_success runtime leaks
    bounds plan inputs horizon scheduler remaining original owner left material event candidate raw
      rfl member request payload binding checks outputEq codeEq node
  have image := frame.live.successful_opening leftBinding.active rightBinding.active
    binding value successful
  obtain ⟨other, sameAccepted, imageAccepted, _owned, _originalFixed, imageFixed⟩ := image.2
  have handles : candidate = other := Option.some.inj (accepted.symm.trans sameAccepted)
  subst other
  have rightFixed : repaired.application.current.native.candidates.lookup candidate =
      .openable raw := by rw [typed]; exact imageFixed
  let message := PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
    (original.observe app owner) material
  have permitted : PhaseCount.permits (app.outputs (original.recall owner)) message = true := by
    have allowed := member
    rw [PhaseCount.mem_onePacketActions] at allowed
    rcases allowed.2 with impossible | ⟨other, transmitted, permitted⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact permitted
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  have named : message.payload.packet.call = .opening event candidate raw :=
    PhaseCount.maskPacket_call _ _
  rw [named] at correct
  obtain ⟨certified, _resolves⟩ := correct
  have physicalCertificate : message.payload.packet.evidence = some ⟨candidate, raw⟩ := by
    unfold certifiedOpening at certified
    rw [named] at certified
    cases found : message.payload.packet.evidence with
    | none => simp only [found, Bool.false_eq_true] at certified
    | some fact =>
        simp only [found, decide_eq_true_eq] at certified
        exact congrArg some certified
  have envelope := PhaseCount.localEnvelope_eq_of_recall runtime leaks original
    countLeft.1 countLeft.2.1 owner material
  have emittedCertificate :
      (material.emit original.application.current.native owner
        ((original.network.known owner).map PhaseCount.nativeMessage)).evidence =
          some ⟨candidate, raw⟩ := by
    have same := congrArg (fun packet : Message Player (CommitAttemptPacket graph) =>
      packet.payload.packet.evidence) envelope
    change message.payload.packet.evidence =
      (original.application.emit owner (original.network.known owner) material).packet.evidence
        at same
    rw [phase_emit_evidence] at same
    exact same.symm.trans physicalCertificate
  have canonicalCertificate :
      (WitnessedSubmission.mk ⟨.opening event candidate raw, none⟩ evidence |>.emit
        (execution runtime leaks original).application owner
          ((execution runtime leaks original).network.known owner)).evidence =
            some ⟨candidate, raw⟩ := by
    change (WitnessedSubmission.mk ⟨.opening event candidate raw, none⟩ evidence |>.emit
      original.application.current.native owner
        ((PhaseBindingRepair.network original.network).known owner)).evidence = _
    rw [network_known]
    exact emittedCertificate
  have native := frame.live.opening_submission event candidate raw evidence rightFixed
    canonicalCertificate
  have packets :
      material.emit original.application.current.native owner
          ((original.network.known owner).map PhaseCount.nativeMessage) =
        material.emit repaired.application.current.native owner
          ((repaired.network.known owner).map PhaseCount.nativeMessage) := by
    have histories := congrArg MessageNetwork.inputs native.network
    change (execution runtime leaks original).network.inputs ++ [_] =
      (execution runtime leaks repaired).network.inputs ++ [_] at histories
    have sameInputs := congrArg MessageNetwork.inputs frame.live.network
    rw [sameInputs] at histories
    have singleton := List.singleton_injective (List.append_cancel_left histories)
    have emitted := congrArg Message.payload singleton
    change (WitnessedSubmission.mk ⟨.opening event candidate raw, none⟩ evidence |>.emit
        original.application.current.native owner
          ((PhaseBindingRepair.network original.network).known owner)) =
      (WitnessedSubmission.mk ⟨.opening event candidate raw, none⟩ evidence |>.emit
        repaired.application.current.native owner
          ((PhaseBindingRepair.network repaired.network).known owner)) at emitted
    rw [network_known, network_known] at emitted
    exact emitted
  exact frame.inert_response bounds countLeft countRight material rfl rfl packets member

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
