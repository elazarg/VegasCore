/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseTimelyResolution
import Vegas.Pending.PhaseCountUniqueness
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.PhaseNativeInvariant
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveReceipts

/-! # A timely counted request can resolve only through its unique envelope -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem timely_request_loss_accepts
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (before : (app).Control)
    (trace : ((app).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (allowed : ∀ packet ∈ before.execution.network.inputs, packet.sender = owner →
      Permits before.execution.network.inputs packet)
    (requested : before.execution.application.SeedRequest owner coordinate)
    (timely : before.execution.application.current.native.WithinDeadline runtime coordinate.event)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ before.execution.network.inputs) (sender : message.sender = owner)
    (attempt : message.payload.attempt = coordinate.attempt)
    (named : message.payload.packet.call.event? graph = some coordinate.event)
    (after : (app).Execution) (command : (app).Command)
    (moved : after ∈ (before.execution.environmentStep app command).support)
    (lost : ¬ after.application.SeedRequest owner coordinate) :
    command = .include message.id ∧
      before.execution.network.lookup message.id = some message ∧
      (app).handle before.execution.application message = some after.application ∧
      (message.id, true) ∈ after.receipts ∧
      ∃ (native : State graph)
        (ready : before.execution.application.current.native.config.cut.Ready coordinate.event)
        (action : graph.Action coordinate.event),
        EventGraphRuntime.handle runtime before.execution.application.current.native
          ⟨message.id, message.payload.packet.call⟩ = some native ∧
        native.config ∈ (before.execution.application.current.native.config.step
          coordinate.event ready action).support ∧
        after.application = ({before.execution.application with
          current := before.execution.application.current.inclusionResult
            message.payload.packet.call native} : PhaseRuntimeState graph).normalize := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    trace
  obtain ⟨identifier, packet, native, ready, action, commandEq, found, packetSender, packetNamed,
      accepted, stepped, normalized⟩ := timely_first_request_loss_includes runtime leaks ordered
    before.execution after valid owner coordinate requested timely command moved lost
  have actualHandle :
      (app).handle before.execution.application packet = some after.application := by
    have applicationEq : after.application =
        ((app).handle before.execution.application packet).getD before.execution.application := by
      have included := moved
      rw [commandEq] at included
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at included
      cases included
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
    cases handled : (app).handle before.execution.application packet with
    | none =>
        rw [handled, Option.getD_none] at applicationEq
        exact (lost (applicationEq.symm ▸ requested)).elim
    | some target =>
        rw [handled, Option.getD_some] at applicationEq
        exact congrArg some applicationEq.symm
  have packetCurrent : packet.payload.attempt = before.execution.application.attempt := by
    by_contra different
    have rejected := before.execution.application.handle_retired runtime packet different
    change before.execution.application.handle runtime packet = some after.application
      at actualHandle
    rw [rejected] at actualHandle
    cases actualHandle
  have envelopes := (app).retained_envelopes_mem_inputs before.execution
    ((app).history_provenance initial horizon scheduler trace)
    ((app).history_inputRecall initial horizon scheduler trace)
  have packetInput := envelopes.lookup identifier packet found
  have sameEvent : event? message.payload = event? packet.payload := by
    simp only [event?, attempt, named, packetNamed, Option.map_some, packetCurrent, requested.1]
  have same := Permits.eq_of_same_event
    (allowed message input sender) (allowed packet packetInput packetSender) input packetInput
    (fun left leftInput right rightInput same =>
      (app).input_identifier_injective_history initial horizon scheduler before trace left right
        leftInput rightInput same) (sender.trans packetSender.symm) sameEvent
  subst packet
  have identifierEq : message.id = identifier := by
    simpa only [decide_eq_true_eq] using List.find?_some found
  rw [← identifierEq] at commandEq found
  have recordedReceipt : (message.id, true) ∈ after.receipts := by
    have included := moved
    rw [commandEq] at included
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff _ _] at included
    have receipts := congrArg ReactiveApplication.Execution.receipts included
    rw [receipts]
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, actualHandle, Option.isSome_some, List.mem_append, List.mem_singleton, or_true]
  exact ⟨commandEq, found, actualHandle, recordedReceipt, native, ready, action,
    accepted, stepped, normalized⟩

end Vegas.EventGraphRuntime.PhaseCount
