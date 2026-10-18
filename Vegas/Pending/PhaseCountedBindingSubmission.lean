/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingService
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseReadyResolution
import Vegas.Pending.PhaseSeedClockEffects

/-! # Native acceptance of a counted declaration immediately after submission -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem submitted_binding_accepted (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (timely : execution.application.current.native.WithinDeadline runtime event)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (app).Action) ∈ onePacketActions runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner)) :
    let after := execution.respond app owner ⟨some material⟩
    let message : Message Player (app).Payload :=
      ⟨(owner, execution.network.nextSerial owner),
        (app).packet ((app).submit execution.application owner material) owner
          (execution.network.known owner) material⟩
    message ∈ after.network.inputs ∧
      message.payload.packet.call.event? graph = some event ∧
        ∃ next, (app).handle after.application message = some next := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := onePacketMenu runtime leaks bounds
  let after := execution.respond app owner ⟨some material⟩
  let message : Message Player (app).Payload :=
    ⟨(owner, execution.network.nextSerial owner),
      (app).packet ((app).submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  obtain ⟨serial, preparation, evidence, declared, _bounded, _fresh⟩ :=
    onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon scheduler remaining
      owner execution trace event payload binding request material offered
  have call : message.payload.packet.call = .commitment event (owner, .prepared serial) := by
    change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
      (execution.network.known owner) material).packet.call = _
    rw [phase_emit_call, declared]
  have input : message ∈ after.network.inputs := by
    change message ∈ execution.network.inputs ++ [message]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨afterTrace⟩ := menu.trace_respond initial horizon scheduler remaining execution owner
    ⟨some material⟩ trace offered
  have raw := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have afterRequest : after.application.SeedRequest owner ⟨execution.application.attempt, event⟩ :=
    respond_request runtime leaks execution owner ⟨some material⟩ owner _ request
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  change execution.application.current.native.activatedAt event = some entered at stamp
  have afterStamp : after.application.current.native.activatedAt event = some entered :=
    (execution.application.submit_progress owner material valid.active).activated event entered
      stamp afterRequest.2.2.1.1
  have afterTimely : after.application.current.native.WithinDeadline runtime event := by
    rw [State.WithinDeadline, afterStamp,
      PhaseSeedCalendar.respond_clock runtime leaks execution valid owner ⟨some material⟩]
    rw [State.WithinDeadline, stamp] at timely
    exact timely
  have actualRequest : after.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩ := afterRequest
  obtain ⟨_native, next, _handled, _completed, _accepted, _normalized, phaseHandled⟩ :=
    binding_accepted_of_history runtime leaks bounds plan inputs horizon scheduler afterTrace
      message input event (owner, .prepared serial) call actualRequest afterTimely
  exact ⟨input, by rw [call]; rfl, next, phaseHandled⟩

end Vegas.EventGraphRuntime.PhaseCount
