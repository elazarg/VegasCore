/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochAcceptingDelivery
import Vegas.Pending.ReservedEpochFirstOffer
import Vegas.Pending.ReservedEpochActiveSlot

/-! # A genuine first certified response is accepted under reserved service -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem first_response_receipt {length : Nat} (tape : Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime) (family runtime leaks (packetCapacity runtime) tape)).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (entered : Nat)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (stamp : execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨execution.application.attempt, event⟩ (execution.recall owner))
    (clean : PhaseCount.OwnCountClean runtime leaks owner execution)
    (material : WitnessedSubmission graph)
    (certificate : ReadyCall execution.application material.call.packet event)
    (permitted : PhaseCount.OnePacketResponse runtime leaks owner (execution.recall owner)
      (execution.observe app owner) ⟨some material⟩)
    (players : Player → (app).Policy)
    (covered : ∀ past view action, action ∈ (players owner past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks owner past view action)
    (final : (app).Execution)
    (reached : final ∈ ((app).runRounds (family runtime leaks (packetCapacity runtime) tape)
      players remaining (execution.respond app owner ⟨some material⟩)).support) :
    ((owner, execution.network.nextSerial owner), true) ∈ final.receipts := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks (packetCapacity runtime) tape
  let after := execution.respond app owner ⟨some material⟩
  let message : Message Player (app).Payload :=
    ⟨(owner, execution.network.nextSerial owner),
      (app).packet ((app).submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  obtain ⟨draw, state⟩ := activation_state_history runtime leaks (packetCapacity runtime) tape
    plan ordered maximal inputs (executionHorizon runtime) ⟨remaining, some owner, execution⟩ trace
  have valid := state.geometry.valid.1
  have protectedResponse := first_response_protected runtime leaks (packetCapacity runtime)
    (completionCycles runtime) tape activationGap processingGap gaps margin plan ordered maximal
      inputs ⟨remaining, some owner, execution⟩ trace event owner entered request stamp first
  obtain ⟨afterTrace⟩ := (app).raw_trace_respond initial (executionHorizon runtime) scheduler
    remaining execution owner ⟨some material⟩ trace
  have afterRequest : after.application.SeedRequest owner
      ⟨execution.application.attempt, event⟩ :=
    respond_request runtime leaks execution owner ⟨some material⟩ owner _ request
  have afterStamp : after.application.current.native.activatedAt event = some entered :=
    (execution.application.submit_progress owner material valid.active).activated event entered
      stamp afterRequest.2.2.1.1
  have afterClean := PhaseCount.ownCountClean_respond runtime leaks owner owner execution
    ⟨some material⟩ clean (fun _ => Or.inr permitted)
  have afterProcessing : packetCapacity runtime ≤ after.environmentRecall.length %
      cycleWidth (graph := graph) (packetCapacity runtime) := by
    rw [(app).respond_environmentRecall]
    exact active_after_processing runtime leaks (packetCapacity runtime) tape initial
      (executionHorizon runtime) ⟨remaining, some owner, execution⟩ trace owner rfl
  have pending : message ∈ after.network.pending := by
    change message ∈ execution.network.pending ++ [message]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have call : message.payload.packet.call = material.call.packet := by
    change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
      (execution.network.known owner) material).packet.call = _
    rw [phase_emit_call]
  have afterCertificate := ReadyCall.respond runtime leaks execution owner ⟨some material⟩
    state.geometry.valid.2.1 (request.1.symm.trans afterRequest.1) material.call.packet event
      certificate
  have packetCertificate : ReadyCall after.application message.payload.packet.call event := by
    rw [call]
    exact afterCertificate
  have protection : after.application.current.native.clock - entered + (processingGap + 1) <
      runtime.deadline event := by
    rw [PhaseSeedCalendar.respond_clock runtime leaks execution valid owner ⟨some material⟩]
    exact protectedResponse.1
  exact protected_pending_receipt runtime leaks tape activationGap processingGap gaps
    players plan ordered maximal inputs remaining after final afterTrace afterProcessing message
      pending event packetCertificate entered afterRequest afterStamp protection afterClean covered
        reached

end Vegas.EventGraphRuntime.ReservedEpoch
