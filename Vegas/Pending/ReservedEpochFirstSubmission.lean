/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochFirstOffer
import Vegas.Pending.PhaseCountedSurvivor
import Vegas.Pending.PhaseOpeningMenuShape

/-! # Handler admissibility of the first counted response at a protected offer -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- This is immediate handler admissibility. Physical delivery and preservation
until the processing epoch are separate obligations. -/
theorem implementation_first_submission_admissible {length : Nat}
    (packetBudget cycles : Nat) (prior : PMF (Tape Player length))
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support, tape.BoundedGaps cycles activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan))
      (cycles * cycleWidth (graph := graph) packetBudget)
        (implementation runtime leaks packetBudget prior).scheduler).Trace
          (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (entered : Nat)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (activated : execution.application.current.native.activatedAt event = some entered)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner
      ⟨execution.application.attempt, event⟩ (execution.recall owner))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (app).Action) ∈
      (PhaseCount.onePacketMenu runtime leaks bounds).actions owner (execution.recall owner)
        (execution.observe app owner)) :
    let after := execution.respond app owner ⟨some material⟩
    let message : Message Player (app).Payload :=
      ⟨(owner, execution.network.nextSerial owner),
        (app).packet ((app).submit execution.application owner material) owner
          (execution.network.known owner) material⟩
    message ∈ after.network.inputs ∧
      message.payload.packet.call.event? graph = some event ∧
        ∃ next, (app).handle after.application message = some next := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := (implementation runtime leaks packetBudget prior).scheduler
  let physicalHorizon := cycles * cycleWidth (graph := graph) packetBudget
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let after := execution.respond app owner ⟨some material⟩
  let message : Message Player (app).Payload :=
    ⟨(owner, execution.network.nextSerial owner),
      (app).packet ((app).submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  have raw := menu.toRawTrace initial physicalHorizon scheduler trace
  have timely := (implementation_first_response_protected runtime leaks packetBudget cycles prior
    activationGap processingGap gaps margin plan ordered maximal inputs
      ⟨remaining, some owner, execution⟩ raw event owner entered request activated first).2
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs physicalHorizon
    scheduler raw
  obtain ⟨afterTrace⟩ := menu.trace_respond initial physicalHorizon scheduler remaining execution
    owner ⟨some material⟩ trace offered
  have afterRequest : after.application.SeedRequest owner
      ⟨execution.application.attempt, event⟩ :=
    respond_request runtime leaks execution owner ⟨some material⟩ owner _ request
  have afterStamp : after.application.current.native.activatedAt event = some entered :=
    (execution.application.submit_progress owner material valid.active).activated event entered
      activated afterRequest.2.2.1.1
  have afterTimely : after.application.current.native.WithinDeadline runtime event := by
    rw [State.WithinDeadline, afterStamp,
      PhaseSeedCalendar.respond_clock runtime leaks execution valid owner ⟨some material⟩]
    rwa [State.WithinDeadline, activated] at timely
  have input : message ∈ after.network.inputs := by
    change message ∈ execution.network.inputs ++ [message]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have named : message.payload.packet.call.event? graph = some event := by
    change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
      (execution.network.known owner) material).packet.call.event? graph = _
    rw [phase_emit_call]
    exact PhaseCount.onePacket_event_of_request runtime leaks bounds plan ordered inputs
      physicalHorizon scheduler remaining owner execution trace
        ⟨execution.application.attempt, event⟩ request material offered
  obtain ⟨native, next, _completed, _normalized, handled⟩ :=
    PhaseCount.counted_call_resolves_of_history runtime leaks bounds plan inputs physicalHorizon
      scheduler afterTrace message input event named afterRequest afterTimely
  exact ⟨input, named, next, handled⟩

end Vegas.EventGraphRuntime.ReservedEpoch
