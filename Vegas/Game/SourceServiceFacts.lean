module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService
public import Vegas.Game.SourceServiceFreshCall
public import Vegas.EventGraph.SolitaryEvent
public import Vegas.Pending.ReactiveSignedCommitments
public import Vegas.Pending.ReactiveEventStability
public import Vegas.Pending.ReactiveAssociationEvidence
public import Vegas.Pending.ReactivePacketEvidence
public import Vegas.Pending.ReactiveStateInvariant
public import Vegas.Pending.ReactiveSubmissionRecall
public import Vegas.Pending.EventCommandFrame
public import Interaction.ReactiveProvenance
public import Interaction.ReactiveMessageIdentity
public import Interaction.ReactiveAllocation
public import Interaction.ReactiveReceipts

@[expose] public section

/-! # Raw initialized service-history facts

Readiness, fixed binding meanings, authentic evidence, recall and packet identities follow
from the native operations at every initialized history. They require no reserved schedule,
source policy, factorization or successful public guards.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- The initial native law is the image of the existing typed setup inputs. -/
theorem serviceInitialLaw_eq_inputs :
    serviceInitialLaw setup deps =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := serviceGraph setup deps)) := by
  rw [PMF.map_comp]
  rfl

/-- Every fresh submission of `who` was made at its own turn at its event. -/
def OwnSubmissionsAtTurn (execution : (serviceApplication setup deps duration leaks).Execution)
    (who : Player) : Prop := ∀ entry ∈ execution.logs who, ∀ event,
    (submittedEvent? (serviceTimeouts setup deps duration)) leaks entry.action = some event →
    entry.beforeView.application.publicView.ownTurn? who = some event

/-- The native facts used to transport acceptable recorded calls. -/
structure LegalFacts (execution : (serviceApplication setup deps duration leaks).Execution) :
    Prop where
  stable : EntryStable (serviceTimeouts setup deps duration) leaks execution
  eventStable : EntryEventStable (serviceTimeouts setup deps duration) leaks execution
  storeStable : EntryStoreStable (serviceTimeouts setup deps duration) leaks execution
  binding : execution.application.BindingInvariant
  evidence : ((packetEvidence (serviceTimeouts setup deps duration)) leaks).Sound execution
  receipts : execution.ReceiptsSound (serviceApplication setup deps duration leaks) (fun _ => True)
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  provenance : execution.Provenance (serviceApplication setup deps duration leaks)
  inputs : execution.InputRecall (serviceApplication setup deps duration leaks)
  quiescent : ∀ event, ¬ execution.application.AutomaticReady event

/-- Every initialized raw history supplies these facts under arbitrary responses and scheduler. -/
theorem legalFacts (horizon : Nat)
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (control : (serviceApplication setup deps duration leaks).Control)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace (some control)) :
    LegalFacts setup leaks control.execution := by
  let app := serviceApplication setup deps duration leaks
  have nativeTrace := trace
  rw [serviceInitialLaw_eq_inputs setup] at nativeTrace
  have receipts := (app.receiptServiceInvariant (fun _ => True) (fun _ => True)
    ⟨by intros; trivial, by intros; trivial, by intros; trivial⟩
    (by intros; trivial) scheduler).history (serviceInitialLaw setup deps) horizon
      (fun state _ => ⟨trivial, app.receiptsSound_initial (fun _ => True) state⟩) trace
  exact {
    stable := entryStable_history (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler trace
    eventStable := entryEventStable_history (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler trace
    storeStable := entryStoreStable_history (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler trace
    binding := (reactiveBindingInvariant_history (serviceTimeouts setup deps duration)) leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace
    evidence := ((packetEvidence (serviceTimeouts setup deps duration)) leaks).history_sound
      (serviceInitialLaw setup deps) horizon scheduler trace
    receipts := receipts.2
    serials := app.serialsBeforeNext_history scheduler (serviceInitialLaw setup deps) horizon trace
    unique := app.uniqueIds_history scheduler (serviceInitialLaw setup deps) horizon control trace
    provenance := app.history_provenance (serviceInitialLaw setup deps) horizon scheduler trace
    inputs := app.history_inputRecall (serviceInitialLaw setup deps) horizon scheduler trace
    quiescent := (reactive_history_quiescent (serviceTimeouts setup deps duration)) leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace }

omit [DecidableEq Player] in
private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ R left right →
      ∀ b ∈ right, ∃ a ∈ left, R a b
  | [], [], .nil, _, member => by simp at member
  | a :: left, b :: right, .cons head tail, x, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨a, List.mem_cons_self, head⟩
      · obtain ⟨y, inside, related⟩ := forall₂_mem_right tail x member
        exact ⟨y, List.mem_cons_of_mem _ inside, related⟩

/-- No receipt names an identifier not yet allocated. -/
theorem no_receipt_next (execution : (serviceApplication setup deps duration leaks).Execution)
    (sound : execution.ReceiptsSound (serviceApplication setup deps duration leaks) (fun _ => True))
    (serials : execution.network.SerialsBeforeNext) (who : Player) (accepted : Bool) :
    ((who, execution.network.nextSerial who), accepted) ∉ execution.receipts := by
  intro member
  obtain ⟨message, published, same, _⟩ := forall₂_mem_right sound _ member
  have bound := serials.ledger message published
  rw [← same] at bound
  exact Nat.lt_irrefl _ bound

/-- The entry a response appends to its author's recall. A fresh submission
emits the author's next identifier. -/
theorem respond_recall_self (execution : (serviceApplication setup deps duration leaks).Execution)
    (who : Player) (action : (serviceApplication setup deps duration leaks).Action) : ∃ emitted,
    (execution.respond (serviceApplication setup deps duration leaks) who action).logs who =
    execution.logs who ++
    [⟨execution.observe (serviceApplication setup deps duration leaks) who, action, emitted⟩] ∧ ∀
    material, action.transmission = some material → ∀ message,
        emitted = some message → message.id = (who, execution.network.nextSerial who) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      exact ⟨none, by simp [ReactiveApplication.Execution.respond], by simp⟩
  | some material =>
      refine
          ⟨some (execution.network.submit who
              ((serviceApplication setup deps duration leaks).packet
              ((serviceApplication setup deps duration leaks).submit execution.application who
              material) who (execution.network.known who) material)).1, by simp only
              [ReactiveApplication.Execution.respond, ↓reduceIte], ?_⟩
      rintro _ ⟨⟩ message ⟨⟩
      rfl

private theorem settled_congr {event : (serviceGraph setup deps).EventId} {id : MessageId Player}
    {before after : (serviceApplication setup deps duration leaks).Execution}
    (configEq : after.application.config = before.application.config)
    (receiptsEq : after.receipts = before.receipts)
    (settled : Settled setup leaks event id before) : Settled setup leaks event id after := by
  unfold Settled
  rw [configEq, receiptsEq]
  exact settled

/-- A response preserves the settlement invariant. -/
theorem settlesFreshCalls_respond (owner : Player) (event : (serviceGraph setup deps).EventId)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (facts : LegalFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup deps duration leaks).Action)
    (valid : SettlesFreshCalls setup leaks owner event bound execution) :
    SettlesFreshCalls setup leaks owner event bound
      (execution.respond (serviceApplication setup deps duration leaks) who action) := by
  let app := serviceApplication setup deps duration leaks
  have configEq :=
      ((reactive_respond_application (serviceTimeouts setup deps duration)) leaks execution who
          action).1
  have receiptsEq := app.respond_receipts execution who action
  intro earlier entry later message split call sole
  apply settled_congr setup leaks configEq receiptsEq
  by_cases same : who = owner
  · subst who
    obtain ⟨emitted, recallEq, idOf⟩ := respond_recall_self setup leaks execution owner action
    rw [recallEq] at split
    rcases List.eq_nil_or_concat later with rfl | ⟨init, last, rfl⟩
    · obtain ⟨_, entryEq⟩ := List.append_inj' split rfl
      have newEntry := (List.singleton_inj.mp entryEq).symm
      subst newEntry
      obtain ⟨material, submitted⟩ := call.fresh
      have idEq := idOf material submitted message call.emitted
      have readyNow : execution.application.config.cut.Ready event :=
        (execution.application.publicView_eventReady event).mp call.ready
      refine ⟨fun finished => (readyNow.1 finished).elim, fun accepted member => ?_,
        fun member => ?_⟩
      · rw [idEq] at member
        exact (no_receipt_next setup leaks execution facts.receipts facts.serials owner accepted
          member).elim
      · rw [idEq] at member
        exact (no_receipt_next setup leaks execution facts.receipts facts.serials owner true
          member).elim
    · simp only [List.concat_eq_append] at split sole
      have reassociated : earlier ++ entry :: (init ++ [last]) =
          (earlier ++ entry :: init) ++ [last] := by simp
      rw [reassociated] at split
      obtain ⟨older, _⟩ := List.append_inj' split rfl
      exact valid earlier entry init message older call fun other member =>
        sole other (by
          rcases List.mem_append.mp member with inside | inside
          · exact List.mem_append_left _ inside
          · exact List.mem_append_right _ (List.mem_append_left _ inside))
  · rw [app.respond_recall_other execution who owner (Ne.symm same) action] at split
    exact valid earlier entry later message split call sole

/-- A recorded response that saw an owner's event ready, which is still
ready, saw it as the owner's turn: every other event of the owner that the
response saw ready is either still ready or has completed while ready together
with this one, and an owner has at most one ready event. -/
theorem ownTurn?_of_entry_ready
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (eventStable : EntryEventStable (serviceTimeouts setup deps duration) leaks execution)
    (who : Player) (entry : (serviceApplication setup deps duration leaks).PlayerEntry)
    (member : entry ∈ execution.logs who) (event : (serviceGraph setup deps).EventId)
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (owned : (serviceGraph setup deps).actor? event = some who)
    (seen : entry.beforeView.application.publicView.EventReady event)
    (ready : execution.application.config.cut.Ready event) :
    entry.beforeView.application.publicView.ownTurn? who = some event := by
  obtain ⟨extra, order, together, _, _⟩ := eventStable who entry member event seen ready.1
  apply PublicView.ownTurn?_of_ownTurn
  refine ⟨seen, owned, fun other otherSeen otherOwned => ?_⟩
  by_cases done : other ∈ execution.application.config.cut.completed
  · have inExtra : other ∈ extra := by
      have inOrder : other ∈ execution.application.publicView.observation.completionOrder :=
        (execution.application.config.history_exact other).mpr done
      rw [order] at inOrder
      rcases List.mem_append.mp inOrder with old | new
      · exact (otherSeen.1 old).elim
      · exact new
    obtain ⟨cut, otherReady, eventReady⟩ := together other inExtra
    exact ownerSolitary.ready_actor_unique cut eventReady otherReady owned otherOwned
  · exact ownerSolitary.ready_actor_unique execution.application.config.cut ready
      (ready_of_eventReady_extends order otherSeen done) owned otherOwned


/-- A pending authentic envelope names a submission already retained in its
sender's recall. It can therefore be attributed before an inclusion attempt. -/
theorem eventRecorded_of_pending
    {horizon : Nat} {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (message : Message Player (WitnessedPacket (serviceGraph setup deps)))
    (member : message ∈ control.execution.network.pending)
    (sender : message.sender = owner)
    (named : message.payload.call.event? (serviceGraph setup deps) = some event) :
    (eventRecorded (serviceTimeouts setup deps duration)) leaks
      (control.execution.logs owner) event = true := by
  have signed := signedCommitments_history (serviceTimeouts setup deps duration) leaks
    (serviceInitialLaw setup deps) (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  obtain ⟨entry, remembered, material, transmitted, emitted, _⟩ :=
    signed.provenance.pending message member
  rw [sender] at remembered
  obtain ⟨_, actual, sent, call⟩ := signed.emissions owner entry remembered message emitted
  apply ((eventRecorded_iff (serviceTimeouts setup deps duration)) leaks
    (control.execution.logs owner) event).mpr
  refine ⟨entry, remembered, ?_⟩
  unfold EventGraphRuntime.submittedEvent?
  rw [sent]
  change actual.call.packet.event? (serviceGraph setup deps) = some event
  rw [← call]
  exact named


section SolitaryWaiting

open EventGraph
variable {setup}

private theorem pending_waiting_call_rejected
    (timeouts : EventTimeouts (serviceGraph setup deps))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (event : (serviceGraph setup deps).EventId) (solitary :
      (serviceGraph setup deps).Solitary event)
    (ready : execution.application.config.cut.Ready event)
    (owner : Player) (owned : (serviceGraph setup deps).actor? event = some owner)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (serviceGraph setup deps) ≠ some event)
    (message : Message Player (WitnessedPacket (serviceGraph setup deps)))
    (pending : message ∈ execution.network.pending) :
    ((reactiveApplication timeouts) leaks).handle execution.application message = none := by
  apply reactiveHandle_none
  cases handled : handle timeouts execution.application ⟨message.id, message.payload.call⟩ with
  | none => rfl
  | some next =>
      obtain ⟨query, named, queryReady, _action, _moved⟩ :=
        handle_config_mem_step timeouts execution.application next _ handled
      have same := solitary _ queryReady ready
      subst query
      have authored := handle_sender_actor timeouts execution.application next _ handled event named
      have sender : message.sender = owner := Option.some.inj (authored.symm.trans owned)
      exact (safe message pending sender named).elim

private theorem native_waiting_config (timeouts : EventTimeouts (serviceGraph setup deps))
    (state next : EventGraphRuntime.State (serviceGraph setup deps))
    (operation : EnvironmentCommand (serviceGraph setup deps))
    (event : (serviceGraph setup deps).EventId) (solitary :
      (serviceGraph setup deps).Solitary event)
    (ready : state.config.cut.Ready event)
    (owner : Player) (owned : (serviceGraph setup deps).actor? event = some owner)
    (within : state.WithinDeadline timeouts event)
    (quiescent : ∀ query, ¬ state.AutomaticReady query)
    (moved : next ∈ (environmentStep timeouts state operation).support) :
    next.drain.config = state.config := by
  have unfinished : event ∉ next.config.cut.completed := by
    by_cases other : operation ≠ .expire event
    · exact fun done => ready.1 ((environmentStep_owned_completed_iff timeouts state next operation
        event owner owned other moved).mp done)
    · have expires : operation = .expire event := by simpa only [not_not] using other
      subst operation
      cases activated : state.activatedAt event with
      | none => simp only [EventGraphRuntime.State.WithinDeadline, activated] at within
      | some entered =>
          have beforeDue : state.clock - entered < timeouts.duration event := by
            simpa only [EventGraphRuntime.State.WithinDeadline, activated] using within
          rw [environmentStep_expire_of_not_due timeouts state event ready entered activated
            (Nat.not_le.mpr beforeDue), PMF.mem_support_pure_iff] at moved
          cases moved
          exact ready.1
  have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
    (fun _ otherReady => solitary _ otherReady ready)
    unfinished (environmentStep_graph_steps timeouts state next operation moved)
  have cleared : ∀ query, ¬ next.AutomaticReady query := by
    simpa only [EventGraphRuntime.State.AutomaticReady, same] using quiescent
  exact (congrArg EventGraphRuntime.State.config (next.drain_eq_of_clear cleared)).trans same

/-- Before its deadline, no environment command changes the unique ready owned
configuration when the network has no call from that owner naming that event. -/
theorem environment_waiting_config_of_solitary
    (timeouts : EventTimeouts (serviceGraph setup deps))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (event : (serviceGraph setup deps).EventId) (solitary :
      (serviceGraph setup deps).Solitary event)
    (owner : Player)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (within : execution.application.WithinDeadline timeouts event)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (serviceGraph setup deps) ≠ some event)
    (reached : next ∈
      (execution.environmentStep ((reactiveApplication timeouts) leaks) command).support) :
    next.application.config = execution.application.config := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      rfl
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      cases found : execution.network.lookup id with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
      | some message =>
          have rejected := pending_waiting_call_rejected timeouts leaks execution event solitary
            ready owner owned safe message (List.mem_of_find?_eq_some found)
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, rejected, Option.getD_none]
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep timeouts execution.application operation).map
        EventGraphRuntime.State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      exact native_waiting_config timeouts execution.application native operation event solitary
        ready owner owned within quiescent nativeMoved


/-- Before its deadline, no environment command changes the unique ready owned
configuration when the network has no call from that owner naming that event. -/
theorem environment_waiting_config (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (execution next : (application setup timeouts leaks).Execution)
    (command : (application setup timeouts leaks).Command)
    (event : setup.informationGraph.EventId) (owner : Player)
    (ready : execution.application.config.cut.Ready event)
    (owned : setup.informationGraph.actor? event = some owner)
    (within : execution.application.WithinDeadline timeouts event)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? setup.informationGraph ≠ some event)
    (reached : next ∈
      (execution.environmentStep (application setup timeouts leaks) command).support) :
    next.application.config = execution.application.config :=
  environment_waiting_config_of_solitary timeouts leaks execution next command event
    (setup.informationGraph.sequentialize_solitary event) owner ready owned within quiescent safe
    reached

end SolitaryWaiting

end Vegas
