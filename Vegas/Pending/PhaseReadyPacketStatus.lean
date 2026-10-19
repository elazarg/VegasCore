/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingReceiptResolution
import Vegas.Pending.PhaseCountMenu
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveInvariantPrefix
import Interaction.ReactiveReceiptIdentity
import Interaction.ReactiveRecordedResponse

/-! # Literal sent status of a still-ready physical request -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A real active callback must record its response before a later idle
control. Even a silent response strictly extends that owner's literal recall. -/
theorem phase_active_idle_recall_lt (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (final : (menu.protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior final) (owner : Player)
    (acting : before.actor = some owner) (idle : after.actor = none) :
    (before.execution.recall owner).length < (after.execution.recall owner).length := by
  have along : ∀ {first last : ((app).protocol initial horizon scheduler).History} {fuel : Nat},
      ((app).protocol initial horizon scheduler).ReachesWithin fuel first last →
      ∀ (before after : (app).Control), first.state = some before → last.state = some after →
        before.actor = some owner → after.actor = none →
          (before.execution.recall owner).length < (after.execution.recall owner).length := by
    intro first last fuel path before after firstEq lastEq acting idle
    cases path with
    | refl _ history =>
        have equal := Option.some.inj (firstEq.symm.trans lastEq)
        subst after
        rw [acting] at idle
        cases idle
    | @step steps history target joint legal reached supported suffix =>
        have moved := supported
        change reached ∈ ((app).transition initial horizon scheduler first.state joint).support
          at moved
        rw [firstEq] at moved
        rcases before with ⟨remaining, actor, execution⟩
        cases acting
        let response := (joint owner).getD ⟨none⟩
        have middleEq : reached = some
            (⟨remaining, none, execution.respond app owner response⟩ : (app).Control) :=
          (PMF.mem_support_pure_iff _ _).mp moved
        have recalled := (app).reaches_recall_prefix initial horizon scheduler suffix
          ⟨remaining, none, execution.respond app owner response⟩ after middleEq lastEq owner
        obtain ⟨emitted, appended⟩ := (app).respond_recall_entry execution owner response
        have bounded := recalled.length_le
        rw [appended, List.length_append, List.length_singleton] at bounded
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) bounded
  exact along (menu.reaches_raw initial horizon scheduler kept.reachesWithin) before after rfl rfl
    acting idle

/-- A resolved physical coordinate stays resolved along a literal counted
history prefix. The actual initialized native invariants supply the premises
of the existing resolution relation. -/
theorem phase_resolved_prefix (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (prior : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before))
    (final : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some after))
    (kept : GameTheory.Protocol.ExecutionProtocol.TracePrefix prior final)
    (coordinate : CommitAttemptEvent graph) (resolved : coordinate.Resolved
      before.execution.application) :
    coordinate.Resolved after.execution.application := by
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    (menu.toRawTrace _ horizon scheduler prior)
  have ordered := (phaseApplication_seedOrder runtime leaks).history _ horizon scheduler
    (fun state selected => by
      obtain ⟨input, _positive, rfl⟩ := PMF.support_map .. ▸ selected
      exact PhaseRuntimeState.initial_ordered plan input)
    (menu.toRawTrace _ horizon scheduler prior)
  let preservation : (app).Invariant (fun state => state.Invariant draw ∧ state.Ordered ∧
      coordinate.Resolved state) := {
    submit := fun state who material old =>
      ⟨(phaseApplication_invariant runtime leaks draw).submit state who material old.1,
        (phaseApplication_seedOrder runtime leaks).submit state who material old.2.1,
        (phaseApplication_resolution runtime leaks coordinate).submit state who material draw
          old.1 old.2.1 old.2.2⟩
    handle := fun state message next old accepted =>
      ⟨(phaseApplication_invariant runtime leaks draw).handle state message next old.1 accepted,
        (phaseApplication_seedOrder runtime leaks).handle state message next old.2.1 accepted,
        (phaseApplication_resolution runtime leaks coordinate).handle state message next accepted
          draw old.1 old.2.1 old.2.2⟩
    environment := fun state command next old reached =>
      ⟨(phaseApplication_invariant runtime leaks draw).environment state command next old.1 reached,
        (phaseApplication_seedOrder runtime leaks).environment state command next old.2.1 reached,
        (phaseApplication_resolution runtime leaks coordinate).environment state command next
          reached draw old.1 old.2.1 old.2.2⟩ }
  exact (preservation.tracePrefix menu _ horizon scheduler before after prior final kept
    ⟨valid, ordered, resolved⟩).2.2

/-- A previously emitted packet for a still-ready request is either actually
pending or has its permanent FALSE physical receipt. A TRUE receipt would have
resolved this exact physical address. No payload/guard success is inferred. -/
theorem phase_seedRequest_sent_status (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some current))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : current.execution.application.SeedRequest owner coordinate)
    (sent : ¬ ∀ message ∈ (app).outputs (current.execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate) :
    ∃ message ∈ current.execution.network.inputs, message.sender = owner ∧
      message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event ∧
      (message ∈ current.execution.network.pending ∨
        (message.id, false) ∈ current.execution.receipts) := by
  classical
  push Not at sent
  obtain ⟨message, member, named⟩ := sent
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  have recalled := (app).history_inputRecall initial horizon scheduler raw owner
  rw [← recalled] at member
  obtain ⟨input, authored⟩ := List.mem_filter.mp member
  have sender : message.sender = owner := of_decide_eq_true authored
  have coordinateEq : ∃ event : graph.EventId,
      message.payload.packet.call.event? graph = some event ∧
      (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph) = coordinate := by
    cases called : message.payload.packet.call.event? graph with
    | none => simp only [PhaseCount.event?, called, Option.map_none] at named; cases named
    | some event => exact ⟨event, rfl, Option.some.inj (by
        simpa only [PhaseCount.event?, called, Option.map_some] using named)⟩
  obtain ⟨event, called, coordinateEq⟩ := coordinateEq
  have address : message.payload.attempt = coordinate.attempt :=
    congrArg CommitAttemptEvent.attempt coordinateEq
  have eventEq : event = coordinate.event := congrArg CommitAttemptEvent.event coordinateEq
  have namedEvent : message.payload.packet.call.event? graph = some coordinate.event := by
    simpa only [eventEq] using called
  refine ⟨message, input, sender, address, namedEvent, ?_⟩
  rcases ((app).pendingOrPublished_history scheduler initial horizon raw).inputs message input with
    pending | published
  · exact Or.inl pending
  · have identifiers := (app).receipt_identifiers_history initial horizon scheduler current raw
    have recorded : message.id ∈ current.execution.receipts.map Prod.fst := by
      rw [identifiers]
      exact List.mem_map.mpr ⟨message, published, rfl⟩
    obtain ⟨receipt, receiptMember, equalId⟩ := List.mem_map.mp recorded
    have actualReceipt : (message.id, receipt.2) ∈ current.execution.receipts := by
      simpa only [← equalId, Prod.mk.eta] using receiptMember
    cases accepted : receipt.2 with
    | false => exact Or.inr (by rwa [accepted] at actualReceipt)
    | true =>
        rw [accepted] at actualReceipt
        exact (PhaseService.not_bindingAccepted_of_request runtime leaks plan inputs horizon
          scheduler raw coordinate owner request
            ⟨message, input, sender, address, namedEvent, actualReceipt⟩).elim


/-- An actual counted input is the sole owned packet at its physical event.
Thus the generic ready-request acceptance predicate reads its literal TRUE
receipt, for bindings and openings alike. -/
theorem phase_counted_packet_receipt_iff [Fintype Player] (bounds : MessageBounds graph)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ current.execution.network.inputs) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (sender : message.sender = owner)
    (address : message.payload.attempt = coordinate.attempt)
    (named : message.payload.packet.call.event? graph = some coordinate.event) :
    PhaseService.BindingAccepted runtime leaks coordinate owner current.execution ↔
      (message.id, true) ∈ current.execution.receipts := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  constructor
  · rintro ⟨other, otherInput, otherSender, otherAddress, otherNamed, receipt⟩
    have first := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 other otherInput)
    have second := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)
    have identified : other = message := PhaseCount.Permits.eq_of_same_event first second
      otherInput input (fun first firstInput second secondInput ids =>
        (app).input_identifier_injective_history initial horizon scheduler current raw
          first second firstInput secondInput ids) (otherSender.trans sender.symm) (by
        simp only [PhaseCount.event?, otherNamed, named, otherAddress, address, Option.map_some])
    simpa only [identified] using receipt
  · intro receipt
    exact ⟨message, input, sender, address, named, receipt⟩

/-- Permanent physical rejection rules out acceptance of the exact counted
coordinate. No alternative envelope at that event can rescue the address. -/
theorem phase_counted_rejected_packet [Fintype Player] (bounds : MessageBounds graph)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ current.execution.network.inputs) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (sender : message.sender = owner)
    (address : message.payload.attempt = coordinate.attempt)
    (named : message.payload.packet.call.event? graph = some coordinate.event)
    (rejected : (message.id, false) ∈ current.execution.receipts) :
    ¬ PhaseService.BindingAccepted runtime leaks coordinate owner current.execution := by
  intro accepted
  have receipt := (phase_counted_packet_receipt_iff runtime leaks bounds initial horizon scheduler
    current trace message input owner coordinate sender address named).mp accepted
  exact (app).rejected_identifier_not_accepted initial horizon scheduler current
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace)
      message.id rejected receipt

end Vegas.EventGraphRuntime
