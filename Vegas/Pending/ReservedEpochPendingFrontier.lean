/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingAcceptedReceipt
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhasePacketAddress
import Vegas.Pending.PhaseCurrentTokens
import Vegas.Pending.PhaseSeedPhysicalIsolation
import Vegas.Pending.PhaseCountUniqueness
import Vegas.Pending.PhaseArchiveGeneration
import Interaction.ReactiveReceiptBoundary

/-! # A counted pending binding belongs to its surviving owner's frontier -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every counted packet bearing the current commitment namespace is a
binding call in that very static block. The original emission phase, rather
than a guessed phase from the current payload, supplies this classification. -/
theorem current_commitment_packet (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph) (installed : phase ∈ control.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ control.execution.network.inputs)
    (current : message.payload.attempt = control.execution.application.attempt) :
    ∃ event candidate, message.payload.packet.call = .commitment event candidate ∧
      event ∈ phase.events := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have allowed := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)
  obtain ⟨origin, originMember, event, named, inside, address⟩ :=
    PhaseCount.packetPhaseOrigins_history runtime leaks plan bounds inputs horizon scheduler
      trace message input
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler raw
  have phaseMember : phase ∈ plan.phases := suffix.subset (List.mem_of_mem_head? installed)
  have low : control.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, Option.mem_def.mp installed, Option.map_some,
      Option.getD_some]
  have same : origin = phase := plan.phase_eq_of_low_eq origin phase originMember phaseMember
    (address.symm.trans ((congrArg CommitAttemptId.phase current).trans low))
  subst origin
  obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
  obtain ⟨owner, payload, binding⟩ := by
    simpa only [commitment] using phase.fields event lower upper
  have correct := allowed.2.1
  cases call : message.payload.packet.call with
  | commitment actual candidate =>
      have eventEq : actual = event := Option.some.inj (by simpa only [call, Payload.event?]
        using named)
      exact ⟨actual, candidate, rfl, eventEq.symm ▸ inside⟩
  | malformed rawValue =>
      simp only [call, Payload.event?] at named
      cases named
  | opening actual candidate rawValue =>
      have eventEq : actual = event := Option.some.inj (by simpa only [call, Payload.event?]
        using named)
      subst actual
      cases node : nodeView graph event with
      | sample sort law outputEq codeEq => cases outputEq.symm.trans binding
      | resolve who sort ref checks outputEq codeEq => cases outputEq.symm.trans binding
      | bind who sort outputEq codeEq =>
          simp only [CountCallCorrect, PhaseCount.nativeMessage, call, node] at correct
          exact correct.2.elim


/-- A surviving owner's pending current-attempt binding has not completed.
Completed surviving bindings have actual accepting receipts; FIRST identifies
their signed envelope, contradicting the pending/receipted separation. -/
theorem pending_binding_unfinished (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ control.execution.network.pending)
    (current : message.payload.attempt = control.execution.application.attempt)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (active : message.sender ∉ control.execution.application.current.excluded) :
    event ∉ control.execution.application.current.native.config.cut.completed := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have envelopes := (app).retained_envelopes_mem_inputs control.execution
    ((app).history_provenance initial horizon scheduler raw)
    ((app).history_inputRecall initial horizon scheduler raw)
  have input := envelopes.pending message pending
  have allowed := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)
  have correct := allowed.2.1
  simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
  have typed : ∃ payload, graph.outputLayout event = .binding message.sender payload := by
    have owned := correct.1
    cases layout : graph.outputLayout event with
    | publicData payload => simp only [bindingOwnedBy, layout, Bool.false_eq_true] at owned
    | privateInput owner payload =>
        simp only [bindingOwnedBy, layout, Bool.false_eq_true] at owned
    | publication payload => simp only [bindingOwnedBy, layout, Bool.false_eq_true] at owned
    | binding owner payload =>
        have same : owner = message.sender := by
          simpa only [bindingOwnedBy, layout, decide_eq_true_eq, Message.sender] using owned
        subst owner
        exact ⟨payload, rfl⟩
  obtain ⟨payload, binding⟩ := typed
  obtain ⟨sourcePhase, _sourceMember, sourceEvent, sourceNamed, sourceInside, address⟩ :=
    PhaseCount.packetPhaseOrigins_history runtime leaks plan bounds inputs horizon scheduler
      trace message input
  have sameEvent : sourceEvent = event := by
    apply Option.some.inj
    exact sourceNamed.symm.trans (by rw [call]; rfl)
  subst sourceEvent
  have lower : control.execution.application.attempt.phase ≤ event.val := by
    have bound := ((sourcePhase.mem_events event).mp sourceInside).1
    rw [← address, current] at bound
    exact bound
  intro completed
  have coverage := (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    raw).active
  have present : control.execution.application.current.native.accepted (.inr event) ≠ none := by
    intro absent
    have failed := (control.execution.application.current.native.publicView_missedBinding
      event message.sender payload binding).mpr ⟨completed, absent⟩
    exact active (coverage.covered event message.sender
      (graph.actor?_of_outputLayout_binding binding) (Or.inl failed))
  obtain ⟨accepted, installed⟩ := Option.ne_none_iff_exists'.mp present
  have records :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  obtain ⟨acceptedPayload, acceptedTyped⟩ := records.accepted_typed (.inr event) accepted installed
  have ownerEq : accepted.1 = message.sender :=
    (EventField.binding.inj (acceptedTyped.symm.trans binding)).1
  obtain ⟨original, originalInput, originalSender, originalAttempt, originalNamed, received⟩ :=
    phase_live_bindingAccepted runtime leaks plan inputs horizon scheduler raw event lower
      accepted installed
  have same : original = message := PhaseCount.Permits.eq_of_same_event
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 original originalInput)) allowed
    originalInput input
    (fun first firstInput second secondInput ids =>
      (app).input_identifier_injective_history initial horizon scheduler control raw
        first second firstInput secondInput ids)
    (originalSender.trans ownerEq)
    (by
      have addressed : original.payload.packet.call.event? graph = some event := originalNamed
      change (original.payload.packet.call.event? graph).map
          (fun event => (⟨original.payload.attempt, event⟩ : CommitAttemptEvent graph)) =
        (message.payload.packet.call.event? graph).map
          (fun event => (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph))
      rw [addressed, call]
      simp only [Payload.event?, Option.map_some, originalAttempt, current])
  rw [same] at received
  exact (app).pending_identifier_not_receipted initial horizon scheduler control raw
    message pending true received

/-- A current pending binding names the owner's actual ready coordinate,
including when it was sent at an older callback and is now late. -/
theorem pending_binding_event_eq (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : control.execution.application.SeedRequest owner coordinate)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ control.execution.network.pending) (sender : message.sender = owner)
    (current : message.payload.attempt = coordinate.attempt)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate) :
    event = coordinate.event := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have envelopes := (app).retained_envelopes_mem_inputs control.execution
    ((app).history_provenance initial horizon scheduler raw)
    ((app).history_inputRecall initial horizon scheduler raw)
  have input := envelopes.pending message pending
  have allowed := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)
  have sameAttempt := current.trans request.1
  have unfinished := pending_binding_unfinished runtime leaks bounds plan inputs horizon scheduler
    control trace message pending sameAttempt event candidate call (by
      simpa only [sender] using request.2.2.2.2)
  have ready := ready_of_current_authentic_token runtime leaks plan inputs horizon scheduler raw
    message input sameAttempt allowed.1 event (by rw [call]; rfl) unfinished
  have actor : graph.actor? event = some owner := by
    have actual := countCallCorrect_owned_event
      (EarlierOwnPacket (control.execution.network.inputs.map PhaseCount.nativeMessage)
        (PhaseCount.nativeMessage message)) (PhaseCount.nativeMessage message) allowed.2.1
          (by change message.payload.packet.call.event? graph = some event; rw [call]; rfl)
    change graph.actor? event = some message.sender at actual
    exact actual.trans (congrArg some sender)
  exact ordered.ready_actor_unique control.execution.application.current.native.config.cut
    request.2.2.1 ready request.2.2.2.1 actor

/-- All current pending bindings of a still-requesting owner are one complete
signed envelope. Different pending positions cannot be a later owned binding. -/
theorem pending_binding_unique (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : control.execution.application.SeedRequest owner coordinate)
    (first second : Message Player (CommitAttemptPacket graph))
    (firstPending : first ∈ control.execution.network.pending)
    (secondPending : second ∈ control.execution.network.pending)
    (firstSender : first.sender = owner) (secondSender : second.sender = owner)
    (firstAttempt : first.payload.attempt = coordinate.attempt)
    (secondAttempt : second.payload.attempt = coordinate.attempt)
    (firstEvent secondEvent : graph.EventId) (firstCandidate secondCandidate : Handle graph)
    (firstCall : first.payload.packet.call = .commitment firstEvent firstCandidate)
    (secondCall : second.payload.packet.call = .commitment secondEvent secondCandidate) :
    first = second := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have envelopes := (app).retained_envelopes_mem_inputs control.execution
    ((app).history_provenance initial horizon scheduler raw)
    ((app).history_inputRecall initial horizon scheduler raw)
  have firstInput := envelopes.pending first firstPending
  have secondInput := envelopes.pending second secondPending
  have firstEventEq := pending_binding_event_eq runtime leaks bounds plan ordered inputs horizon
    scheduler control trace owner coordinate request first firstPending firstSender firstAttempt
      firstEvent firstCandidate firstCall
  have secondEventEq := pending_binding_event_eq runtime leaks bounds plan ordered inputs horizon
    scheduler control trace owner coordinate request second secondPending secondSender secondAttempt
      secondEvent secondCandidate secondCall
  exact PhaseCount.Permits.eq_of_same_event
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 first firstInput))
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 second secondInput))
    firstInput secondInput
    (fun left leftInput right rightInput same =>
      (app).input_identifier_injective_history initial horizon scheduler control raw
        left right leftInput rightInput same)
    (firstSender.trans secondSender.symm)
    (by simp only [PhaseCount.event?, firstCall, secondCall, Payload.event?, Option.map_some,
      firstAttempt, secondAttempt, firstEventEq, secondEventEq])

/-- At most one current-attempt owner packet appears in an actual pending
queue around its selected frontier. Every other own backlog envelope is stale;
this conclusion includes both the preceding and following FIFO portions. -/
theorem pending_frontier_surroundings (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph) (installed : phase ∈ control.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : control.execution.application.SeedRequest owner coordinate)
    (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = owner) (current : message.payload.attempt = coordinate.attempt)
    (preceding suffix : List (Message Player (CommitAttemptPacket graph)))
    (pending : control.execution.network.pending = preceding ++ message :: suffix) :
    (∀ packet ∈ preceding, packet.sender ≠ owner ∨ packet.payload.attempt ≠ coordinate.attempt) ∧
      (∀ packet ∈ suffix, packet.sender ≠ owner ∨ packet.payload.attempt ≠ coordinate.attempt) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have envelopes := (app).retained_envelopes_mem_inputs control.execution
    ((app).history_provenance initial horizon scheduler raw)
    ((app).history_inputRecall initial horizon scheduler raw)
  have messagePending : message ∈ control.execution.network.pending := by
    rw [pending]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨event, candidate, call, _inside⟩ := current_commitment_packet runtime leaks bounds plan
    inputs horizon scheduler control trace phase installed commitment message
      (envelopes.pending message messagePending) (current.trans request.1)
  have distinct := (app).idsDistinct_history scheduler initial horizon raw
  change ((control.execution.network.pending ++ control.execution.network.ledger).map
    Message.id).Nodup at distinct
  rw [List.map_append] at distinct
  have queueDistinct := (List.nodup_append.mp distinct).1
  rw [pending, List.map_append, List.map_cons] at queueDistinct
  have prefixAbsent : message.id ∉ preceding.map Message.id := by
    intro member
    exact (List.nodup_append.mp queueDistinct).2.2 _ member _ (List.mem_cons_self ..) rfl
  have suffixAbsent : message.id ∉ suffix.map Message.id :=
    (List.nodup_cons.mp (List.nodup_append.mp queueDistinct).2.1).1
  have only (packet : Message Player (CommitAttemptPacket graph))
      (member : packet ∈ control.execution.network.pending)
      (packetSender : packet.sender = owner)
      (packetAttempt : packet.payload.attempt = coordinate.attempt) : packet = message := by
    obtain ⟨packetEvent, packetCandidate, packetCall, _packetInside⟩ := current_commitment_packet
      runtime leaks bounds plan inputs horizon scheduler control trace phase installed commitment
        packet (envelopes.pending packet member) (packetAttempt.trans request.1)
    exact pending_binding_unique runtime leaks bounds plan ordered inputs horizon scheduler
      control trace owner coordinate request packet message member messagePending packetSender
        sender packetAttempt current packetEvent event packetCandidate candidate packetCall call
  constructor
  · intro packet member
    by_cases packetSender : packet.sender = owner
    · right
      intro packetAttempt
      have same := only packet (by rw [pending]; exact List.mem_append_left _ member)
        packetSender packetAttempt
      exact prefixAbsent (same ▸ List.mem_map.mpr ⟨packet, member, rfl⟩)
    · exact Or.inl packetSender
  · intro packet member
    by_cases packetSender : packet.sender = owner
    · right
      intro packetAttempt
      have same := only packet (by
        rw [pending]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ member)) packetSender packetAttempt
      exact suffixAbsent (same ▸ List.mem_map.mpr ⟨packet, member, rfl⟩)
    · exact Or.inl packetSender

/-- Once a surviving owner's complete block word is frozen, every remaining
own pending envelope belongs to a retired namespace. No later FIFO action can
be another genuine current-attempt binding of that owner. -/
theorem completed_owner_pending_stale (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph) (installed : phase ∈ control.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (owner : Player)
    (active : owner ∉ control.execution.application.current.excluded)
    (finished : ∀ event ∈ phase.events, graph.actor? event = some owner →
      event ∈ control.execution.application.current.native.config.cut.completed)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ control.execution.network.pending) (sender : message.sender = owner) :
    message.payload.attempt ≠ control.execution.application.attempt := by
  intro current
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have envelopes := (app).retained_envelopes_mem_inputs control.execution
    ((app).history_provenance initial horizon scheduler raw)
    ((app).history_inputRecall initial horizon scheduler raw)
  have input := envelopes.pending message pending
  obtain ⟨event, candidate, call, inside⟩ := current_commitment_packet runtime leaks bounds plan
    inputs horizon scheduler control trace phase installed commitment message input current
  have allowed := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)
  have actor : graph.actor? event = some owner := by
    have actual := countCallCorrect_owned_event
      (EarlierOwnPacket (control.execution.network.inputs.map PhaseCount.nativeMessage)
        (PhaseCount.nativeMessage message)) (PhaseCount.nativeMessage message) allowed.2.1
          (by change message.payload.packet.call.event? graph = some event; rw [call]; rfl)
    change graph.actor? event = some message.sender at actual
    exact actual.trans (congrArg some sender)
  exact pending_binding_unfinished runtime leaks bounds plan inputs horizon scheduler control
    trace message pending current event candidate call (by simpa only [sender] using active)
      (finished event inside actor)

end Vegas.EventGraphRuntime.ReservedEpoch
