/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Game.SourceServiceFreshCall
import Vegas.EventGraph.SolitaryEvent
import Vegas.Pending.ReactiveSignedCommitments
import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveSubmissionRecall
import Vegas.Pending.EventCommandFrame
import Interaction.ReactiveProvenance
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveAllocation
import Interaction.ReactiveReceipts

/-! # Raw initialized service-history facts

Readiness, fixed binding meanings, authentic evidence, recall and packet identities follow
from the native operations at every initialized history. They require no reserved schedule,
source policy, factorization or successful public guards.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The initial native law is the image of the existing typed setup inputs. -/
theorem serviceInitialLaw_eq_inputs :
    serviceInitialLaw setup mode =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)) := by
  rw [PMF.map_comp]
  rfl

/-- Every fresh submission of `who` was made at its own turn at its event. -/
def OwnSubmissionsAtTurn (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) : Prop := ∀ entry ∈ execution.logs who, ∀ event,
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
    entry.beforeView.application.publicView.ownTurn? who = some event

/-- The native facts used to transport acceptable recorded calls. -/
structure LegalFacts (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop where
  stable : EntryStable (serviceRuntime setup mode deadline) leaks execution
  eventStable : EntryEventStable (serviceRuntime setup mode deadline) leaks execution
  storeStable : EntryStoreStable (serviceRuntime setup mode deadline) leaks execution
  binding : execution.application.BindingInvariant
  evidence : ((serviceRuntime setup mode deadline).packetEvidence leaks).Sound execution
  receipts : execution.ReceiptsSound (serviceApplication setup mode deadline leaks) (fun _ => True)
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  provenance : execution.Provenance (serviceApplication setup mode deadline leaks)
  inputs : execution.InputRecall (serviceApplication setup mode deadline leaks)
  quiescent : ∀ event, ¬ execution.application.AutomaticReady event

/-- Every initialized raw history supplies these facts under arbitrary responses and scheduler. -/
theorem legalFacts (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control)) :
    LegalFacts setup leaks control.execution := by
  let app := serviceApplication setup mode deadline leaks
  have nativeTrace := trace
  rw [serviceInitialLaw_eq_inputs setup] at nativeTrace
  have receipts := (app.receiptServiceInvariant (fun _ => True) (fun _ => True)
    ⟨by intros; trivial, by intros; trivial, by intros; trivial⟩
    (by intros; trivial) scheduler).history (serviceInitialLaw setup mode) horizon
      (fun state _ => ⟨trivial, app.receiptsSound_initial (fun _ => True) state⟩) trace
  exact {
    stable := entryStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    eventStable := entryEventStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    storeStable := entryStoreStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    binding := (serviceRuntime setup mode deadline).reactiveBindingInvariant_history leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace
    evidence := ((serviceRuntime setup mode deadline).packetEvidence leaks).history_sound
      (serviceInitialLaw setup mode) horizon scheduler trace
    receipts := receipts.2
    serials := app.serialsBeforeNext_history scheduler (serviceInitialLaw setup mode) horizon trace
    unique := app.uniqueIds_history scheduler (serviceInitialLaw setup mode) horizon control trace
    provenance := app.history_provenance (serviceInitialLaw setup mode) horizon scheduler trace
    inputs := app.history_inputRecall (serviceInitialLaw setup mode) horizon scheduler trace
    quiescent := (serviceRuntime setup mode deadline).reactive_history_quiescent leaks
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
theorem no_receipt_next (execution : (serviceApplication setup mode deadline leaks).Execution)
    (sound : execution.ReceiptsSound (serviceApplication setup mode deadline leaks) (fun _ => True))
    (serials : execution.network.SerialsBeforeNext) (who : Player) (accepted : Bool) :
    ((who, execution.network.nextSerial who), accepted) ∉ execution.receipts := by
  intro member
  obtain ⟨message, published, same, _⟩ := forall₂_mem_right sound _ member
  have bound := serials.ledger message published
  rw [← same] at bound
  exact Nat.lt_irrefl _ bound

/-- The entry a response appends to its author's recall. A fresh submission
emits the author's next identifier. -/
theorem respond_recall_self (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) (action : (serviceApplication setup mode deadline leaks).Action) : ∃ emitted,
    (execution.respond (serviceApplication setup mode deadline leaks) who action).logs who =
    execution.logs who ++
    [⟨execution.observe (serviceApplication setup mode deadline leaks) who, action, emitted⟩] ∧ ∀
    material, action.transmission = some material → ∀ message,
        emitted = some message → message.id = (who, execution.network.nextSerial who) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      exact ⟨none, by simp [ReactiveApplication.Execution.respond], by simp⟩
  | some material =>
      refine
          ⟨some (execution.network.submit who
              ((serviceApplication setup mode deadline leaks).packet
              ((serviceApplication setup mode deadline leaks).submit execution.application who
              material) who (execution.network.known who) material)).1, by simp only
              [ReactiveApplication.Execution.respond, ↓reduceIte], ?_⟩
      rintro _ ⟨⟩ message ⟨⟩
      rfl

private theorem settled_congr {event : (serviceGraph setup mode).EventId} {id : MessageId Player}
    {before after : (serviceApplication setup mode deadline leaks).Execution}
    (configEq : after.application.config = before.application.config)
    (receiptsEq : after.receipts = before.receipts)
    (settled : Settled setup leaks event id before) : Settled setup leaks event id after := by
  unfold Settled
  rw [configEq, receiptsEq]
  exact settled

/-- A response preserves the settlement invariant. -/
theorem settlesFreshCalls_respond (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (facts : LegalFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action)
    (valid : SettlesFreshCalls setup leaks owner event bound execution) :
    SettlesFreshCalls setup leaks owner event bound
      (execution.respond (serviceApplication setup mode deadline leaks) who action) := by
  let app := serviceApplication setup mode deadline leaks
  have configEq :=
      ((serviceRuntime setup mode deadline).reactive_respond_application leaks execution who
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
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (eventStable : EntryEventStable (serviceRuntime setup mode deadline) leaks execution)
    (who : Player) (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (member : entry ∈ execution.logs who) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (seen : entry.beforeView.application.publicView.EventReady event)
    (ready : execution.application.config.cut.Ready event) :
    entry.beforeView.application.publicView.ownTurn? who = some event := by
  have relaxed := serviceGraph_revealRelaxedOrdered setup mode
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
    exact relaxed.ready_actor_unique cut eventReady otherReady owned otherOwned
  · exact relaxed.ready_actor_unique execution.application.config.cut ready
      (ready_of_eventReady_extends order otherSeen done) owned otherOwned


/-- A pending authentic envelope names a submission already retained in its
sender's recall. It can therefore be attributed before an inclusion attempt. -/
theorem eventRecorded_of_pending
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (member : message ∈ control.execution.network.pending)
    (sender : message.sender = owner)
    (named : message.payload.call.event? (serviceGraph setup mode) = some event) :
    (serviceRuntime setup mode deadline).eventRecorded leaks
      (control.execution.logs owner) event = true := by
  have signed := signedCommitments_history (serviceRuntime setup mode deadline) leaks
    (serviceInitialLaw setup mode) (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  obtain ⟨entry, remembered, material, transmitted, emitted, _⟩ :=
    signed.provenance.pending message member
  rw [sender] at remembered
  obtain ⟨_, actual, sent, call⟩ := signed.emissions owner entry remembered message emitted
  apply ((serviceRuntime setup mode deadline).eventRecorded_iff leaks
    (control.execution.logs owner) event).mpr
  refine ⟨entry, remembered, ?_⟩
  unfold EventGraphRuntime.submittedEvent?
  rw [sent]
  change actual.call.packet.event? (serviceGraph setup mode) = some event
  rw [← call]
  exact named


section SolitaryWaiting

open EventGraph
variable {setup}

private theorem pending_waiting_call_rejected
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (event : (serviceGraph setup mode).EventId) (solitary :
      (serviceGraph setup mode).Solitary event)
    (ready : execution.application.config.cut.Ready event)
    (owner : Player) (owned : (serviceGraph setup mode).actor? event = some owner)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (serviceGraph setup mode) ≠ some event)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (pending : message ∈ execution.network.pending) :
    (runtime.reactiveApplication leaks).handle execution.application message = none := by
  apply reactiveHandle_none
  cases handled : handle runtime execution.application ⟨message.id, message.payload.call⟩ with
  | none => rfl
  | some next =>
      obtain ⟨query, named, queryReady, _action, _moved⟩ :=
        handle_config_mem_step runtime execution.application next _ handled
      have same := solitary _ queryReady ready
      subst query
      have authored := handle_sender_actor runtime execution.application next _ handled event named
      have sender : message.sender = owner := Option.some.inj (authored.symm.trans owned)
      exact (safe message pending sender named).elim

private theorem native_waiting_config (runtime : EventGraphRuntime (serviceGraph setup mode))
    (state next : EventGraphRuntime.State (serviceGraph setup mode))
    (operation : EnvironmentCommand (serviceGraph setup mode))
    (event : (serviceGraph setup mode).EventId) (solitary :
      (serviceGraph setup mode).Solitary event)
    (ready : state.config.cut.Ready event)
    (owner : Player) (owned : (serviceGraph setup mode).actor? event = some owner)
    (within : state.WithinDeadline runtime event)
    (quiescent : ∀ query, ¬ state.AutomaticReady query)
    (moved : next ∈ (environmentStep runtime state operation).support) :
    next.drain.config = state.config := by
  have unfinished : event ∉ next.config.cut.completed := by
    by_cases other : operation ≠ .expire event
    · exact fun done => ready.1 ((environmentStep_owned_completed_iff runtime state next operation
        event owner owned other moved).mp done)
    · have expires : operation = .expire event := by simpa only [not_not] using other
      subst operation
      cases activated : state.activatedAt event with
      | none => simp only [EventGraphRuntime.State.WithinDeadline, activated] at within
      | some entered =>
          have beforeDue : state.clock - entered < runtime.deadline event := by
            simpa only [EventGraphRuntime.State.WithinDeadline, activated] using within
          rw [environmentStep_expire_of_not_due runtime state event ready entered activated
            (Nat.not_le.mpr beforeDue), PMF.mem_support_pure_iff] at moved
          cases moved
          exact ready.1
  have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
    (fun _ otherReady => solitary _ otherReady ready)
    unfinished (environmentStep_graph_steps runtime state next operation moved)
  have cleared : ∀ query, ¬ next.AutomaticReady query := by
    simpa only [EventGraphRuntime.State.AutomaticReady, same] using quiescent
  exact (congrArg EventGraphRuntime.State.config (next.drain_eq_of_clear cleared)).trans same

/-- Before its deadline, no environment command changes the unique ready owned
configuration when the network has no call from that owner naming that event. -/
theorem environment_waiting_config_mode (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (event : (serviceGraph setup mode).EventId) (solitary :
      (serviceGraph setup mode).Solitary event)
    (owner : Player)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (within : execution.application.WithinDeadline runtime event)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (serviceGraph setup mode) ≠ some event)
    (reached : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) command).support) :
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
          have rejected := pending_waiting_call_rejected runtime leaks execution event solitary
            ready owner owned safe message (List.mem_of_find?_eq_some found)
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, rejected, Option.getD_none]
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep runtime execution.application operation).map
        EventGraphRuntime.State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      exact native_waiting_config runtime execution.application native operation event solitary
        ready owner owned within quiescent nativeMoved


/-- Before its deadline, no environment command changes the unique ready owned
configuration when the network has no call from that owner naming that event. -/
theorem environment_waiting_config (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution next : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command)
    (event : (graph setup).EventId) (owner : Player)
    (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (within : execution.application.WithinDeadline runtime event)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event)
    (reached : next ∈
      (execution.environmentStep (application setup runtime leaks) command).support) :
    next.application.config = execution.application.config :=
  environment_waiting_config_mode runtime leaks execution next command event
    (setup.eventGraph.sequentialize_solitary event) owner ready owned within quiescent safe reached

end SolitaryWaiting

end Vegas
