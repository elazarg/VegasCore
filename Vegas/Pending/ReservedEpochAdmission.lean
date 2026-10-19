/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingService
import Vegas.Pending.PhaseOpeningService
import Vegas.Pending.PhaseAcceptedProgress

/-! # Concrete binding and truthful opening certificates for reserved delivery -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The message is either a binding or an opening of its current accepted
native candidate. This certificate does not assert handler acceptance. -/
inductive ReadyCall (state : PhaseRuntimeState graph)
    (packet : Payload graph) (event : graph.EventId) : Prop
  | binding (candidate : Handle graph)
      (call : packet = .commitment event candidate)
  | opening (owner : Player) (payload : L.Ty)
      (binding : FieldRef graph.layout (.binding owner payload))
      (checks : List (GuardCheck graph.layout payload))
      (outputEq : graph.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
        .resolve owner payload binding checks)
      (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
      (candidate : Handle graph) (raw : Raw L)
      (call : packet = .opening event candidate raw)
      (associated : state.current.native.accepted binding.field = some candidate)

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem readyCall_accepts (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (physicalHorizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) physicalHorizon
      scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ control.execution.network.inputs) (event : graph.EventId)
    (certificate : ReadyCall control.execution.application message.payload.packet.call event)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime event)
    (clean : ∀ packet ∈ control.execution.network.inputs, packet.sender = message.sender →
      PhaseCount.permits control.execution.network.inputs packet = true) :
    ∃ next, (app).handle control.execution.application message = some next := by
  cases certificate with
  | binding candidate call =>
      obtain ⟨native, next, _handled, _completed, _installed, _normalized, accepted⟩ :=
        PhaseCount.binding_accepted_of_own_history runtime leaks plan inputs physicalHorizon
          scheduler trace message.sender clean message input rfl event candidate call request timely
      exact ⟨next, accepted⟩
  | opening owner payload binding checks outputEq codeEq node candidate raw call associated =>
      obtain ⟨native, next, _handled, _completed, _normalized, accepted⟩ :=
        PhaseCount.opening_accepted_of_certificate runtime leaks plan inputs physicalHorizon
          scheduler
          trace message input event candidate raw call request timely (clean message input rfl)
            owner payload binding checks outputEq codeEq node associated
      exact ⟨next, accepted⟩

theorem ReadyCall.respond (execution : (app).Execution) (owner : Player) (action : (app).Action)
    (ordered : execution.application.Ordered)
    (same : execution.application.attempt =
      (execution.respond app owner action).application.attempt)
    (packet : Payload graph) (event : graph.EventId)
    (certificate : ReadyCall execution.application packet event) :
    ReadyCall (execution.respond app owner action).application packet event := by
  cases certificate with
  | binding candidate call => exact .binding candidate call
  | opening actor payload binding checks outputEq codeEq node candidate raw call associated =>
      exact .opening actor payload binding checks outputEq codeEq node candidate raw call
        ((PhaseRuntimeState.accepted_progress runtime leaks).respond execution owner action ordered
          same binding.field candidate associated)

theorem ReadyCall.environment {before after : (app).Execution}
    (command : (app).Command)
    (moved : after ∈ (before.environmentStep app command).support)
    (ordered : before.application.Ordered)
    (same : before.application.attempt = after.application.attempt)
    (packet : Payload graph) (event : graph.EventId)
    (certificate : ReadyCall before.application packet event) :
    ReadyCall after.application packet event := by
  cases certificate with
  | binding candidate call => exact .binding candidate call
  | opening owner payload binding checks outputEq codeEq node candidate raw call associated =>
      exact .opening owner payload binding checks outputEq codeEq node candidate raw call
        ((PhaseRuntimeState.accepted_progress runtime leaks).environmentStep before after command
          moved ordered same binding.field candidate associated)

theorem ReadyCall.runRounds (players : Player → (app).Policy) (scheduler : (app).Scheduler)
    (count : Nat) (before after : (app).Execution) (ordered : before.application.Ordered)
    (reached : after ∈ ((app).runRounds scheduler players count before).support)
    (same : before.application.attempt = after.application.attempt)
    (packet : Payload graph) (event : graph.EventId)
    (certificate : ReadyCall before.application packet event) :
    ReadyCall after.application packet event := by
  cases certificate with
  | binding candidate call => exact .binding candidate call
  | opening owner payload binding checks outputEq codeEq node candidate raw call associated =>
      exact .opening owner payload binding checks outputEq codeEq node candidate raw call
        (phase_runRounds_accepted runtime leaks players scheduler count before after ordered reached
          same binding.field candidate associated)

end Vegas.EventGraphRuntime.ReservedEpoch
