/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochAcceptingDelivery
import Vegas.Pending.PhaseBindingAcceptedReceipt
import Vegas.Pending.ReservedEpochActiveSlot
import Interaction.ReactiveReceiptBoundary

/-! # An accepting event receipt precedes its original deadline -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem input_mem_runRounds (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (before after : (app).Execution)
    (message : Message Player (app).Payload) (input : message ∈ before.network.inputs)
    (reached : after ∈ ((app).runRounds scheduler players count before).support) :
    message ∈ after.network.inputs := by
  have invariant : (app).PolicyInvariant players
      (fun execution => message ∈ execution.network.inputs) := {
    respond := by
      intro execution owner response known _supported
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => exact known
      | some material => exact List.mem_append_left _ known
    environment := by
      intro execution next command known moved
      rwa [(app).environmentStep_inputs execution next command moved] }
  exact invariant.runRounds scheduler count before after input reached

omit [Fintype Player] in
private theorem handle_event_ready_timely (state native : State graph)
    (id : MessageId Player) (packet : Payload graph) (event : graph.EventId)
    (named : packet.event? graph = some event)
    (handled : handle runtime state ⟨id, packet⟩ = some native) :
    state.config.cut.Ready event ∧ state.WithinDeadline runtime event := by
  cases packet with
  | malformed raw => cases named
  | commitment selected candidate | opening selected candidate raw =>
      have same : selected = event := Option.some.inj named
      subst selected
      by_cases ready : state.config.cut.Ready event
      · refine ⟨ready, ?_⟩
        by_contra late
        simp only [handle, dite_eq_left ready, dite_eq_right late] at handled
        cases handled
      · simp only [handle, dite_eq_right ready] at handled
        cases handled

omit [Fintype Player] in
theorem accepting_include_native (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control)) (next : (app).Execution)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ control.execution.network.inputs)
    (absent : (message.id, true) ∉ control.execution.receipts)
    (moved : next ∈ (control.execution.environmentStep app (.include message.id)).support)
    (accepted : (message.id, true) ∈ next.receipts) :
    ∃ native following,
      control.execution.application.handle runtime message = some following ∧
      handle runtime control.execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
  cases (PMF.mem_support_pure_iff ..).mp moved
  cases found : control.execution.network.lookup message.id with
  | none =>
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] at accepted
      exact (absent accepted).elim
  | some actual =>
      have pending : actual ∈ control.execution.network.pending := List.mem_of_find?_eq_some found
      have actualInput := ((app).retained_envelopes_mem_inputs control.execution
        ((app).history_provenance _ horizon scheduler trace)
        ((app).history_inputRecall _ horizon scheduler trace)).pending actual pending
      have sameId : actual.id = message.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      have same : actual = message := (app).input_identifier_injective_history _ horizon
        scheduler control trace actual message actualInput input sameId
      subst actual
      cases handled : control.execution.application.handle runtime message with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, show (app).handle control.execution.application message = none from handled,
            Option.isSome_none, List.mem_append, List.mem_singleton, Prod.mk.injEq,
            Bool.true_eq_false, and_false, or_false] at accepted
          exact (absent accepted).elim
      | some following =>
          obtain ⟨native, nativeHandled, _normalized, _receipts, _rawStamp⟩ :=
            phase_inclusion_snapshot_bindingAccepted runtime leaks plan inputs horizon scheduler
              trace message.id message found following handled
          exact ⟨native, following, rfl, nativeHandled⟩

/-- Any eventual true receipt of this original pending event packet forces the
first next marked epoch to be inside its original entered-time deadline.
The statement covers old late episodes and arbitrary raw future players. -/
theorem pending_receipt_requires_timely_epoch {length : Nat}
    (packetBudget : Nat) (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon remaining : Nat)
    (before final : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (family runtime leaks packetBudget tape)).Trace (some ⟨remaining, none, before⟩))
    (sentCycle slot : Nat)
    (cursor : before.environmentRecall.length =
      sentCycle * cycleWidth (graph := graph) packetBudget + slot)
    (afterProcessing : packetBudget ≤ slot)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ before.network.pending) (event : graph.EventId)
    (named : message.payload.packet.call.event? graph = some event)
    (request : before.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (entered : Nat) (stamp : before.application.current.native.activatedAt event = some entered)
    (reached : final ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      remaining before).support) (accepted : (message.id, true) ∈ final.receipts) :
    ∃ epoch, tape.nextProcessingEpoch (sentCycle + 1) = some epoch ∧
      epoch * cycleWidth (graph := graph) packetBudget < horizon ∧
      epoch - entered < runtime.deadline event := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks packetBudget tape
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    trace
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (fun state positive => by
      obtain ⟨input, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact PhaseRuntimeState.initial_ordered plan input) trace
  have input := ((app).retained_envelopes_mem_inputs before
    ((app).history_provenance initial horizon scheduler trace)
    ((app).history_inputRecall initial horizon scheduler trace)).pending message pending
  have absent := (app).pending_identifier_not_receipted initial horizon scheduler
    ⟨remaining, none, before⟩ trace message pending true
  obtain ⟨used, tail, prior, middle, lengths, path, unreceipted, included, moved,
    receipted, _future⟩ := (app).runRounds_accepting_receipt_boundary scheduler players remaining
      before final message.id absent reached accepted
  have usedLe : used ≤ remaining := by omega
  obtain ⟨priorTrace⟩ := (app).raw_trace_runRounds initial horizon scheduler players
    (remaining - used) used before prior (by
      simpa only [Nat.sub_add_cancel usedLe] using trace) path
  have priorInput := input_mem_runRounds runtime leaks scheduler players used before prior message
    input path
  obtain ⟨native, following, handled, nativeHandled⟩ := accepting_include_native runtime leaks
    plan inputs horizon scheduler ⟨remaining - used, none, prior⟩ priorTrace middle message
      priorInput unreceipted moved receipted
  have live := handle_event_ready_timely runtime prior.application.current.native native
    message.id message.payload.packet.call event named nativeHandled
  have positive : 0 < runtime.deadline event := by
    have timely := live.2
    unfold State.WithinDeadline at timely
    split at timely
    · exact timely.elim
    · omega
  have bound : ClosedCoordinateBound runtime entered entered ⟨message.payload.attempt, event⟩
      before.application :=
    ⟨valid.active.activated_le event entered stamp, le_rfl, by rw [request.1],
      by rw [request.1], fun _ => Or.inr ⟨request.2.2.1, stamp, by simpa using positive⟩⟩
  have retained := PhaseSeedCalendar.retained_bound_runRounds runtime leaks scheduler players
    used before prior valid ordered entered entered ⟨message.payload.attempt, event⟩ bound path
  have sameAttempt := PhaseRuntimeState.handle_attempt_eq runtime prior.application following
    message handled
  have priorStamp : prior.application.current.native.activatedAt event = some entered := by
    rcases retained.event sameAttempt with completed | active
    · exact (live.1.1 completed).elim
    · exact active.2.1
  have extended := (app).runRounds_environmentRecall_length scheduler players used before prior path
  have selected := (family_support runtime leaks packetBudget tape prior.environmentRecall
    (prior.observeEnvironment app) (.include message.id)).mp included
  have processing := include_requires_processing runtime leaks packetBudget tape
    prior.environmentRecall.length (prior.observeEnvironment app) message.id selected.symm
  have starts : sentCycle < prior.environmentRecall.length /
      cycleWidth (graph := graph) packetBudget := by
    by_contra earlier
    have multiplication := Nat.mul_le_mul_right (cycleWidth (graph := graph) packetBudget)
      (Nat.le_of_not_gt earlier)
    have remainder := Nat.mod_add_div prior.environmentRecall.length
      (cycleWidth (graph := graph) packetBudget)
    rw [Nat.mul_comm _ (prior.environmentRecall.length /
      cycleWidth (graph := graph) packetBudget)] at remainder
    omega
  have available : ∃ cycle, sentCycle + 1 ≤ cycle ∧ tape.processes cycle = true :=
    ⟨prior.environmentRecall.length / cycleWidth (graph := graph) packetBudget,
      by omega, processing.2⟩
  let epoch := Nat.find available
  have selectedEpoch : tape.nextProcessingEpoch (sentCycle + 1) = some epoch := by
    simp only [Tape.nextProcessingEpoch, available, ↓reduceDIte]
    rfl
  have spec := tape.nextProcessingEpoch_spec (sentCycle + 1) epoch selectedEpoch
  have quiet : ∀ later, sentCycle < later → later < epoch → tape.processes later = false := by
    intro later lower upper
    cases marked : tape.processes later with
    | false => rfl
    | true => have minimum := spec.2.2 later (by omega) marked; omega
  have notEarlier : epoch * cycleWidth (graph := graph) packetBudget ≤
      prior.environmentRecall.length := by
    by_contra earlier
    exact no_include_between_epochs runtime leaks packetBudget tape sentCycle slot epoch
      afterProcessing quiet prior.environmentRecall.length (prior.observeEnvironment app)
        (by omega) (by omega) message.id selected.symm
  have clock := clock_history runtime leaks packetBudget tape plan inputs horizon
    ⟨remaining - used, none, prior⟩ priorTrace
  have epochBefore : epoch ≤ prior.application.current.native.clock := by
    rw [clock]
    exact (Nat.le_div_iff_mul_le (cycleWidth_pos packetBudget)).mpr notEarlier
  have timely := live.2
  rw [State.WithinDeadline, priorStamp] at timely
  have accounted := (app).raw_trace_horizon initial horizon scheduler trace
  have beforeEnd : prior.environmentRecall.length < horizon := by
    change before.environmentRecall.length + remaining = horizon at accounted
    omega
  exact ⟨epoch, selectedEpoch, notEarlier.trans_lt beforeEnd,
    (Nat.sub_le_sub_right epochBefore entered).trans_lt timely⟩

/-- The actual accepting-receipt bit of an old pending certified packet is exactly its
next shared epoch's deadline comparison. Preparation contents and arbitrary
covered foreign traffic do not enter this operational bit. -/
theorem pending_receipt_iff_timely_epoch {length : Nat} (cycles : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (remaining sentCycle slot : Nat)
    (before final : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (cursor : before.environmentRecall.length = sentCycle *
      cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles) + slot)
    (afterProcessing : submissionBudget (Player := Player) cycles ≤ slot)
    (clock : before.application.current.native.clock = sentCycle)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ before.network.pending) (event : graph.EventId)
    (certificate : ReadyCall before.application message.payload.packet.call event)
    (request : before.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (entered : Nat) (stamp : before.application.current.native.activatedAt event = some entered)
    (clean : PhaseCount.OwnCountClean runtime leaks message.sender before)
    (covered : ∀ past view action, action ∈ (players message.sender past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks message.sender past view action)
    (reached : final ∈ ((app).runRounds
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape) players remaining
        before).support) :
    (message.id, true) ∈ final.receipts ↔
      ∃ epoch, tape.nextProcessingEpoch (sentCycle + 1) = some epoch ∧ epoch < cycles ∧
        epoch - entered < runtime.deadline event := by
  have named : message.payload.packet.call.event? graph = some event := by
    cases certificate <;> simp_all only [Payload.event?]
  constructor
  · intro accepted
    obtain ⟨epoch, selected, within, timely⟩ :=
      pending_receipt_requires_timely_epoch runtime leaks
        (submissionBudget (Player := Player) cycles) tape players plan inputs
        (horizon (graph := graph) cycles) remaining before final trace sentCycle slot cursor
          afterProcessing message pending event named request entered stamp reached
            accepted
    have running : epoch < cycles := by
      change epoch * cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles) <
        cycles * cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles) at within
      by_contra late
      have opposite := Nat.mul_le_mul_right
        (cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles))
          (Nat.le_of_not_gt late)
      omega
    exact ⟨epoch, selected, running, timely⟩
  · rintro ⟨epoch, selectedEpoch, running, inTime⟩
    let initial := inputs.map (PhaseRuntimeState.initial plan)
    let scheduler := family runtime leaks (submissionBudget (Player := Player) cycles) tape
    have orderedBefore := (phaseApplication_seedOrder runtime leaks).history initial
      (horizon (graph := graph) cycles) scheduler (fun state positive => by
        obtain ⟨input, _positive, rfl⟩ := PMF.support_map .. ▸ positive
        exact PhaseRuntimeState.initial_ordered plan input) trace
    have spec := tape.nextProcessingEpoch_spec (sentCycle + 1) epoch selectedEpoch
    have quiet : ∀ later, sentCycle < later → later < epoch → tape.processes later = false := by
      intro later lower upper
      cases marked : tape.processes later with
      | false => rfl
      | true => have minimum := spec.2.2 later (by omega) marked; omega
    have timely : before.application.current.native.WithinDeadline runtime event := by
      rw [State.WithinDeadline, stamp, clock]
      exact (Nat.sub_le_sub_right (by omega : sentCycle ≤ epoch) entered).trans_lt inTime
    exact receipt_at_processing_boundary runtime leaks cycles tape players plan ordered inputs
      remaining sentCycle slot epoch before final trace orderedBefore cursor afterProcessing quiet
        (by omega) running spec.2.1 clock message pending event certificate entered
          request stamp timely inTime clean covered reached

/-- A literal current SEND at a real owner callback has the exact finite
timely-epoch receipt bit. All cursor, packet, namespace and entered-stamp
facts are derived after that actual response. The certificate covers both
bindings and truthful openings, including a semantically rejected guard. -/
theorem current_response_receipt_iff {length : Nat} (cycles : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (entered : Nat)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (stamp : execution.application.current.native.activatedAt event = some entered)
    (material : WitnessedSubmission graph)
    (certificate : ReadyCall execution.application material.call.packet event)
    (clean : PhaseCount.OwnCountClean runtime leaks owner execution)
    (permitted : PhaseCount.OnePacketResponse runtime leaks owner (execution.recall owner)
      (execution.observe app owner) ⟨some material⟩)
    (covered : ∀ past view action, action ∈ (players owner past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks owner past view action) :
    let after := execution.respond app owner ⟨some material⟩
    let message : Message Player (app).Payload :=
      ⟨(owner, execution.network.nextSerial owner),
        (app).packet ((app).submit execution.application owner material) owner
          (execution.network.known owner) material⟩
    ∀ final ∈ ((app).runRounds
        (family runtime leaks (submissionBudget (Player := Player) cycles) tape)
          players remaining after).support,
      ((message.id, true) ∈ final.receipts ↔
        ∃ epoch, tape.nextProcessingEpoch (execution.environmentRecall.length /
            cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles) + 1) =
          some epoch ∧ epoch < cycles ∧ epoch - entered < runtime.deadline event) := by
  intro after message final reached
  let bound := horizon (graph := graph) cycles
  let budget := submissionBudget (Player := Player) cycles
  let scheduler := family runtime leaks budget tape
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨afterTrace⟩ := (app).raw_trace_respond initial bound scheduler remaining execution
    owner ⟨some material⟩ trace
  have afterProcessing := active_after_processing runtime leaks budget tape
    initial bound ⟨remaining, some owner, execution⟩ trace owner rfl
  let sentCycle := execution.environmentRecall.length / cycleWidth (graph := graph) budget
  let slot := execution.environmentRecall.length % cycleWidth (graph := graph) budget
  have cursor : after.environmentRecall.length =
      sentCycle * cycleWidth (graph := graph) budget + slot := by
    have decomposition := Nat.mod_add_div execution.environmentRecall.length
      (cycleWidth (graph := graph) budget)
    rw [Nat.mul_comm (cycleWidth (graph := graph) budget)] at decomposition
    change execution.environmentRecall.length =
      execution.environmentRecall.length / cycleWidth (graph := graph) budget *
        cycleWidth (graph := graph) budget +
          execution.environmentRecall.length % cycleWidth (graph := graph) budget
    omega
  have clock := clock_history runtime leaks budget tape plan inputs bound
    ⟨remaining, none, after⟩ afterTrace
  have afterRequest := respond_request runtime leaks execution owner ⟨some material⟩ owner
    ⟨execution.application.attempt, event⟩ request
  have pending : message ∈ after.network.pending :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have call : message.payload.packet.call = material.call.packet := by
    change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
      (execution.network.known owner) material).packet.call = _
    rw [phase_emit_call]
  have address : message.payload.attempt = execution.application.attempt := rfl
  have authored : message.sender = owner := rfl
  have requestMessage : after.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩ := by
    simpa only [address, authored] using afterRequest
  obtain ⟨_draw, valid⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs bound scheduler trace
  have afterStamp : after.application.current.native.activatedAt event = some entered :=
    (execution.application.submit_progress owner material valid.active).activated event entered
      stamp afterRequest.2.2.1.1
  have orderedBefore := (phaseApplication_seedOrder runtime leaks).history initial bound scheduler
    (fun state positive => by
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact PhaseRuntimeState.initial_ordered plan draw) trace
  have afterCertificate := ReadyCall.respond runtime leaks execution owner ⟨some material⟩
    orderedBefore rfl material.call.packet event certificate
  have packetCertificate : ReadyCall after.application message.payload.packet.call event := by
    rw [call]
    exact afterCertificate
  have afterClean := PhaseCount.ownCountClean_respond runtime leaks owner owner execution
    ⟨some material⟩ clean (fun _ => Or.inr permitted)
  exact pending_receipt_iff_timely_epoch runtime leaks cycles tape players plan ordered inputs
    remaining sentCycle slot after final afterTrace cursor afterProcessing clock message pending
      event packetCertificate requestMessage entered afterStamp
        (by simpa only [authored] using afterClean)
          (by simpa only [authored] using covered) reached

end Vegas.EventGraphRuntime.ReservedEpoch
