/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCheckpointSubmission
import Vegas.Pending.PhaseOpeningAcceptance

/-! # Actual counted openings read successful bindings before inclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Count correctness and actual certificate provenance force the surviving
binding's typed success even before a possibly late opening is included. -/
theorem opening_binding_success (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (opening : message.payload.packet.call = .opening event candidate raw)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq) :
    ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧
      binding.get? control.execution.application.current.native.config.store =
        some (.success value) ∧
      control.execution.application.current.native.accepted binding.field = some candidate ∧
      control.execution.application.current.native.candidates.lookup candidate =
        .openable ⟨payload, value⟩ := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
    scheduler trace
  have invariant := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawTrace
  have covered := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler rawTrace
  have permitted := (PhaseCount.permits_eq_true_iff _ _).mp (physical.clean.2 message member)
  have correct := permitted.2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [opening] at correct
  obtain ⟨certified, resolves⟩ := correct
  have latest := permitted.2.2.2
  unfold PhaseCount.OpeningBinding at latest
  rw [opening] at latest
  simp only [node] at resolves latest
  obtain ⟨sender, typed, _signed⟩ := resolves
  have associated := PhaseCount.accepted_of_latest runtime leaks control.execution physical
    invariant.active covered.active
    (phaseInputBinding_history runtime leaks plan inputs horizon scheduler rawTrace)
    ((phaseApplication runtime leaks).uniqueIds_history scheduler initial horizon control rawTrace)
    message member event candidate raw opening owner payload binding checks outputEq codeEq node
    request.2.2.1 request sender latest
  have certificate : message.payload.packet.evidence = some ⟨candidate, raw⟩ := by
    unfold certifiedOpening at certified
    rw [opening] at certified
    cases evidence : message.payload.packet.evidence with
    | none => simp only [evidence, Bool.false_eq_true] at certified
    | some fact =>
        simp only [evidence, decide_eq_true_eq] at certified
        exact congrArg some certified
  have sound := (phasePacketEvidence runtime leaks).history_sound initial horizon scheduler rawTrace
  have verified := sound.inputs message member ⟨candidate, raw⟩ (by
    simp only [phasePacketEvidence, certificate, Option.toList_some, List.mem_singleton])
  change control.execution.application.current.native.candidates.lookup candidate = .openable raw
    at verified
  rcases raw with ⟨rawType, value⟩
  change rawType = payload at typed
  subst rawType
  exact ⟨value, rfl, invariant.active.opening_stored binding candidate value associated verified,
    associated, verified⟩

/-- An actual counted opening response already reads a successful surviving
binding at its input. Its own legal extension supplies the certificate witness;
neither timely inclusion nor a successful-opening premise is supplied. -/
theorem opening_response_binding_success (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (physical : (phaseApplication runtime leaks).Execution) (owner : Player)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, physical⟩))
    (material : WitnessedSubmission graph) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L) (call : material.call.packet = .opening event candidate raw)
    (member : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (physical.recall owner)
        (physical.observe (phaseApplication runtime leaks) owner))
    (request : physical.application.SeedRequest owner ⟨physical.application.attempt, event⟩)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq) :
    ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧
      binding.get? physical.application.current.native.config.store = some (.success value) ∧
      physical.application.current.native.accepted binding.field = some candidate ∧
      physical.application.current.native.candidates.lookup candidate =
        .openable ⟨payload, value⟩ := by
  let app := phaseApplication runtime leaks
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let submitted := physical.respond app owner ⟨some material⟩
  let message := PhaseCount.localEnvelope runtime leaks owner (physical.recall owner)
    (physical.observe app owner) material
  obtain ⟨postTrace⟩ := (PhaseCount.onePacketMenu runtime leaks bounds).trace_respond initial
    horizon scheduler remaining physical owner ⟨some material⟩ trace member
  have recalled := PhaseCount.countRecall_history runtime leaks
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace)
  have inserted : message ∈ submitted.network.inputs := by
    rw [(PhaseCount.permits_respond runtime leaks physical recalled owner material).1]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have inert : submitted.application = physical.application := by
    rcases material with ⟨⟨packet, preparation⟩, evidence⟩
    change packet = .opening event candidate raw at call
    subst packet
    rfl
  have named : message.payload.packet.call = .opening event candidate raw := by
    change (PhaseCount.maskPacket _ _).call = _
    exact (PhaseCount.maskPacket_call _ _).trans call
  have postRequest : submitted.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩ := by
    rw [inert]
    exact request
  have positive := opening_binding_success runtime leaks bounds plan inputs horizon scheduler
    postTrace message inserted event candidate raw named postRequest owner payload binding checks
      outputEq codeEq node
  have sameApplication :
      (physical.respond (phaseApplication runtime leaks) owner ⟨some material⟩).application =
        physical.application := inert
  simpa only [sameApplication] using positive

end Vegas.EventGraphRuntime.PhaseBindingRepair
