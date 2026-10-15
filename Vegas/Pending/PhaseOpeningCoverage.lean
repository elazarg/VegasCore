/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBoundedHandles
import Vegas.Pending.PhaseOpeningResponse
import Vegas.Pending.PhaseBindingInvariant

/-! # Canonical opening coverage and exact native resolution at phased histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- Every actual unsent opening of a surviving successful binding has an
encodable authentic response. The exact native result includes guard rejection;
no latest-handle, certificate, menu-membership or acceptance premise is supplied. -/
theorem exists_phaseOpeningResponse_of_history
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? control.execution.application.current.native.config.store =
      some (.success value))
    (values : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (timely : control.execution.application.current.native.WithinDeadline runtime event) :
    ∃ candidate,
      control.execution.application.current.native.accepted binding.field = some candidate ∧
      candidate.1 = owner ∧
      control.execution.application.current.native.candidates.lookup candidate =
        .openable ⟨payload, value⟩ ∧
      phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩ ∈
        onePacketActions runtime leaks bounds owner (control.execution.recall owner)
          (control.execution.observe app owner) ∧
      ∃ result, EventCode.resolveOutput? binding checks true
          control.execution.application.current.native.config.store = some result ∧
        handle runtime control.execution.application.current.native
          ⟨(owner, control.execution.network.nextSerial owner),
            .opening event candidate ⟨payload, value⟩⟩ =
          some (control.execution.application.current.native.complete event request.2.2.1
            (cast (congrArg EventField.Action outputEq.symm) true)
            (cast (congrArg EventField.Value outputEq.symm) result)) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := (onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace
  have valid := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have signed := phaseSignedBindings_history runtime leaks plan inputs horizon scheduler raw
  have physical := physicalBindings_history runtime leaks bounds plan inputs horizon scheduler trace
  obtain ⟨candidate, accepted, owned, verified⟩ := valid.active.success_provenance binding value
    stored
  have bounded := (bounds.phaseAcceptedHandles_history runtime leaks
    (onePacketMenu runtime leaks bounds) (onePacketMenu_in_raw runtime leaks bounds)
    plan inputs horizon scheduler trace).2 binding.field candidate accepted
  have permitted := phaseOpeningResponse_permitted runtime leaks control.execution physical
    (fun input candidate installed => Prod.ext rfl (signed.2.1 input candidate installed))
    owner event payload binding checks outputEq codeEq node candidate value owned accepted verified
    request unsent
  refine ⟨candidate, accepted, owned, verified, ?_, ?_⟩
  · rw [mem_onePacketActions]
    refine ⟨?_, Or.inr permitted⟩
    rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    change disclosureSubmission (.opening event candidate ⟨payload, value⟩) ∈ _
    rw [bounds.submissions_mem]
    exact bounds.disclosureSubmission_allowed _ _ ⟨bounded, values⟩
  · have defined := EventCode.resolveOutput?_isSome binding checks true
      control.execution.application.current.native.config.store (by
        intro field read
        apply control.execution.application.current.native.config.read_available request.2.2.1
        rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
        exact read)
    obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp defined
    exact ⟨result, resolved, handle_opening_eq runtime _ _ event candidate owner payload binding
      checks outputEq codeEq node request.2.2.1 timely rfl owned accepted value verified stored
      result resolved⟩

end Vegas.EventGraphRuntime.PhaseCount
