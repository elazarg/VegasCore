/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceCanonicalSerial
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Good packets and retained play

A retained packet is good when it is on track, or accepted with the content the
record accepts (`Vegas.SettledGood`); a good packet is permitted by the settled
record (`Vegas.SettledGood.permits`). Retained play is play with conforming
fresh calls, one submission per event and good emitted packets
(`Vegas.RetainedFacts`). A response keeps a packet good
(`Vegas.SettledGood.respond`). Under a scheduler with protected inclusion, a
scheduler command keeps good every emitted packet sent by its event's actor,
when fresh calls conform and each player submits once per event after the
command (`Vegas.SettledGood.environment`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Content

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The content a packet will settle with if accepted at this state is what the
record accepts. -/
def PendingContent (state : EventGraphRuntime.State (serviceGraph setup mode))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  match message.payload.call with
  | .commitment _ candidate =>
      message.payload.evidence = none ∧
        candidate = (message.sender, .prepared (state.publicView.bindingCount message.sender))
  | .opening _ _ _ =>
      certifiedOpening message.payload = true ∧
        state.publicView.openingGuardsAccepted message.payload = true
  | .malformed _ => False

/-- A retained packet is on track, or accepted with the content the record
accepts. -/
def SettledGood (execution : (serviceApplication setup mode deadline leaks).Execution)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  ∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
    ((execution.application.config.cut.Ready event ∧ (message.id, true) ∉ execution.receipts ∧
        PendingContent setup execution.application message) ∨
      ((message.id, true) ∈ execution.receipts ∧
        event ∈ execution.application.config.cut.completed ∧
        ((serviceRuntime setup mode deadline).settledRecord leaks execution).SettledContent
        message))

variable {setup leaks}

/-- A conforming packet's content is what the record accepts. -/
theorem pendingContent_of_fresh (state : EventGraphRuntime.State (serviceGraph setup mode))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (fresh : (serviceRuntime setup mode deadline).freshServiceEnvelope state.publicView message) :
    PendingContent setup state message := by
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | commitment event candidate =>
      obtain ⟨_, canonical, empty, _⟩ :=
          ((serviceRuntime setup mode deadline).freshServiceEnvelope_binding_iff state.publicView id
              event candidate evidence token).mp fresh
      exact ⟨empty, canonical⟩
  | opening event candidate raw =>
      unfold EventGraphRuntime.freshServiceEnvelope at fresh
      exact ⟨fresh.2.2.1, fresh.2.2.2.1⟩
  | malformed raw => exact fresh.elim

/-- The settled content of a packet for a completed event survives every later
contract step. -/
theorem settledContent_step {before after : EventGraphRuntime.State (serviceGraph setup mode)}
    (step : ContractStep before after)
    (beforeReceipts afterReceipts : List (MessageId Player × Bool))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId)
    (named : message.payload.call.event? (serviceGraph setup mode) = some event)
    (completed : event ∈ before.config.cut.completed)
    (content :
        (⟨before.publicView, beforeReceipts⟩ : SettledRecord
        (serviceGraph setup mode)).SettledContent message) :
    (⟨after.publicView, afterReceipts⟩ : SettledRecord (serviceGraph setup mode)).SettledContent
    message := by
  obtain ⟨rest, extended⟩ := step.order_extends
  have member : event ∈ before.publicView.observation.completionOrder :=
    (before.config.history_exact event).mpr completed
  have guardsEq := State.openingGuardsAccepted_congr before after message.payload event named
    (fun predecessor inside => before.config.cut.predecessor_closed completed inside)
    (fun field value stored => step.store_retained field value stored)
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | malformed raw => exact content.elim
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      obtain ⟨empty, canonical⟩ := content
      refine ⟨empty, ?_⟩
      change candidate = (id.1, .prepared (before.publicView.bindingCountBefore id.1 event))
        at canonical
      change candidate = (id.1, .prepared (after.publicView.bindingCountBefore id.1 event))
      rw [canonical, PublicView.bindingCountBefore_append before.publicView after.publicView id.1
        event member rest extended]
  | opening actual candidate raw =>
      obtain ⟨certified, guarded⟩ := content
      refine ⟨certified, ?_⟩
      change before.publicView.openingGuardsAccepted _ = true at guarded
      change after.publicView.openingGuardsAccepted _ = true
      rw [guardsEq]
      exact guarded

/-- Accepting a packet whose pending content the record accepts settles that
content. -/
theorem settledContent_of_pending (before after : EventGraphRuntime.State (serviceGraph setup mode))
    (receipts : List (MessageId Player × Bool))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId)
    (named : message.payload.call.event? (serviceGraph setup mode) = some event)
    (ready : before.config.cut.Ready event) (action : (serviceGraph setup mode).Action event)
    (member : after.config ∈ (before.config.step event ready action).support)
    (pending : PendingContent setup before message) :
    (⟨after.publicView, receipts⟩ : SettledRecord (serviceGraph setup mode)).SettledContent
    message := by
  have orderEq : after.publicView.observation.completionOrder =
      before.publicView.observation.completionOrder ++ [event] := by
    change after.config.history.map Completion.event =
      before.config.history.map Completion.event ++ [event]
    rw [before.config.step_history event ready action after.config member]
    simp
  have absent : event ∉ before.publicView.observation.completionOrder :=
    fun inside => ready.1 ((before.config.history_exact event).mp inside)
  have guardsEq := State.openingGuardsAccepted_congr before after message.payload event named
    (fun predecessor inside => ready.2 inside)
    (fun field value stored => before.config.step_store_of_some after.config event ready action
      member field value stored)
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | malformed raw => exact pending.elim
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      obtain ⟨empty, canonical⟩ := pending
      refine ⟨empty, ?_⟩
      change candidate = (id.1, .prepared (before.publicView.bindingCount id.1)) at canonical
      change candidate = (id.1, .prepared (after.publicView.bindingCountBefore id.1 event))
      rw [canonical, PublicView.bindingCountBefore_complete before.publicView after.publicView
        id.1 event absent [] orderEq]
  | opening actual candidate raw =>
      obtain ⟨certified, guarded⟩ := pending
      refine ⟨certified, ?_⟩
      change before.publicView.openingGuardsAccepted _ = true at guarded
      change after.publicView.openingGuardsAccepted _ = true
      rw [guardsEq]
      exact guarded

/-- A good packet is permitted by the settled record. -/
theorem SettledGood.permits {execution : (serviceApplication setup mode deadline leaks).Execution}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (good : SettledGood setup leaks execution message) :
    ((serviceRuntime setup mode deadline).settledRecord leaks execution).permits message =
    true := by
  obtain ⟨event, named, ⟨ready, _, _⟩ | ⟨accepted, _, content⟩⟩ := good
  · exact SettledRecord.permits_of_unsettled _ message event named fun inside =>
      ready.1 ((execution.application.config.history_exact event).mp inside)
  · exact SettledRecord.permits_of_accepted _ message event named accepted content

/-- Pending content reads only the public observation. -/
theorem pendingContent_congr {first second : EventGraphRuntime.State (serviceGraph setup mode)}
    (same : second.publicView.observation = first.publicView.observation)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (pending : PendingContent setup first message) : PendingContent setup second message := by
  unfold PendingContent at pending ⊢
  cases call : message.payload.call with
  | commitment event candidate =>
      simp only [call] at pending ⊢
      rw [PublicView.bindingCount_eq_countP, same, ← PublicView.bindingCount_eq_countP]
      exact pending
  | opening event candidate raw =>
      simp only [call] at pending ⊢
      unfold PublicView.openingGuardsAccepted at pending ⊢
      rw [same]
      exact pending
  | malformed raw => simp only [call] at pending

/-- Pending content is kept when another event, ready together with the
packet's event of the packet's author, completes: the author's binding count is
unchanged, and the event's guards do not read the completed output. -/
theorem pendingContent_of_other_step
    {before after : EventGraphRuntime.State (serviceGraph setup mode)}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    {event other : (serviceGraph setup mode).EventId}
    (named : message.payload.call.event? (serviceGraph setup mode) = some event)
    (owned : (serviceGraph setup mode).actor? event = some message.sender)
    (ready : before.config.cut.Ready event) (otherReady : before.config.cut.Ready other)
    (different : other ≠ event) {action : (serviceGraph setup mode).Action other}
    (member : after.config ∈ (before.config.step other otherReady action).support)
    (pending : PendingContent setup before message) : PendingContent setup after message := by
  have historyEq := before.config.step_history other otherReady action _ member
  have orderEq : after.publicView.observation.completionOrder =
      before.publicView.observation.completionOrder ++ [other] := by
    change after.config.history.map EventGraph.Completion.event = _
    rw [historyEq, List.map_append, List.map_singleton]
    rfl
  unfold PendingContent at pending ⊢
  cases call : message.payload.call with
  | commitment actual candidate =>
      simp only [call] at pending ⊢
      refine ⟨pending.1, pending.2.trans ?_⟩
      have foreign : bindingOwnedBy (serviceGraph setup mode) message.sender other = false := by
        obtain ⟨otherOwner, eventOwner, otherActor, eventActor, owners⟩ :=
          (serviceGraph_revealRelaxedOrdered setup mode).ready_pair_actors otherReady ready
            different
        rw [owned] at eventActor
        unfold bindingOwnedBy
        cases kind : (serviceGraph setup mode).outputLayout other with
        | binding owner payload =>
            have actorIs := (serviceGraph setup mode).actor?_of_outputLayout_binding kind
            rw [otherActor] at actorIs
            simp only [decide_eq_false_iff_not]
            intro same
            exact owners ((Option.some.inj actorIs).trans
              (same.trans (Option.some.inj eventActor)))
        | publicData _ => rfl
        | privateInput _ _ => rfl
        | publication _ => rfl
      rw [PublicView.bindingCount_eq_countP, PublicView.bindingCount_eq_countP, orderEq,
        List.countP_append]
      simp [foreign]
  | opening actual candidate raw =>
      simp only [call] at pending ⊢
      refine ⟨pending.1, ?_⟩
      have actualEq : actual = event := by
        change Payload.event? (serviceGraph setup mode) message.payload.call = some event at named
        rw [call] at named
        exact Option.some.inj named
      subst actualEq
      have guards := pending.2
      unfold PublicView.openingGuardsAccepted at guards ⊢
      rw [call] at guards ⊢
      dsimp only at guards ⊢
      cases node : nodeView (serviceGraph setup mode) actual with
      | resolve owner payload binding checks outputEq codeEq =>
          rw [node] at guards
          dsimp only at guards ⊢
          have unread := EventGraph.output_not_mem_reads_of_ready ready otherReady
          have agree : EventGraph.Store.AgreeOn before.publicView.observation.store
              after.publicView.observation.store (EventGraph.GuardCheck.listReadFields checks) := by
            intro field read
            have inNode : field ∈ ((serviceGraph setup mode).nodes actual).readFields := by
              rw [← EventGraph.EventCode.readFields_cast outputEq
                ((serviceGraph setup mode).nodes actual), codeEq]
              exact Finset.mem_insert_of_mem read
            change (serviceGraph setup mode).publicStore before.config.store field =
              (serviceGraph setup mode).publicStore after.config.store field
            unfold EventGraph.publicStore
            rcases EventGraphRuntime.step_store_eq_or_output member field with same | ⟨fieldEq, _⟩
            · rw [same]
            · subst fieldEq
              exact (unread inNode).elim
          simp only [EventGraph.GuardCheck.allAccepted?_congr checks _ _ _ agree] at guards
          exact guards
      | bind _ _ _ _ =>
          rw [node] at guards
          exact guards
      | sample _ _ _ _ =>
          rw [node] at guards
          exact guards
  | malformed raw => simp only [call] at pending

/-- A conforming packet meets the inclusion deadline with no slack. -/
theorem fresh_fits (view : PublicView (serviceGraph setup mode))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId)
    (named : message.payload.call.event? (serviceGraph setup mode) = some event)
    (fresh : (serviceRuntime setup mode deadline).freshServiceEnvelope view message) :
    view.InclusionFitsDeadline (serviceRuntime setup mode deadline) (fun _ => 0) event := by
  have deadline : match view.activatedAt event with
      | none => False
      | some entered => view.clock - entered < (serviceRuntime setup mode deadline).deadline
          event := by
    rcases message with ⟨id, ⟨call, evidence, token⟩⟩
    cases call with
    | commitment actual candidate =>
        change some actual = some event at named
        cases Option.some.inj named
        exact fresh.1.2.1
    | opening actual candidate raw =>
        change some actual = some event at named
        cases Option.some.inj named
        exact fresh.2.1
    | malformed raw => exact fresh.elim
  unfold PublicView.InclusionFitsDeadline
  cases activated : view.activatedAt event with
  | none =>
      rw [activated] at deadline
      exact deadline
  | some entered =>
      rw [activated] at deadline
      simpa only [Nat.add_zero] using deadline

/-- A submission names the event its emitted packet addresses. -/
theorem submittedEvent_of_issued
    {entry : (serviceApplication setup mode deadline leaks).PlayerEntry}
    {material : (serviceApplication setup mode deadline leaks).Submission}
    (transmission : entry.action.transmission = some material)
    {state : EventGraphRuntime.State (serviceGraph setup mode)} {who : Player}
    {known : List (Message Player (WitnessedPacket (serviceGraph setup mode)))}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (packet : (serviceApplication setup mode deadline leaks).packet state who known material =
        message.payload) : (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action =
      message.payload.call.event? (serviceGraph setup mode) := by
  unfold EventGraphRuntime.submittedEvent?
  rw [transmission, ← packet]
  rfl

/-- **Retained packets settle.** Under a scheduler that includes an owner's sole
packet before its event can complete in any other way, when every fresh call
conforms on the view its author saw and each player submits once per event, the
event of every emitted packet completes only by accepting that packet. -/
theorem retained_accepted {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler (fun _ => 0))
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some control))
    (conform : ∀ who, FreshCallsConform setup leaks control.execution who)
    (once : ∀ who, OneCallPerEvent setup leaks control.execution who)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (emitted : Emitted setup leaks control.execution message)
    (event : (serviceGraph setup mode).EventId)
    (named : message.payload.call.event? (serviceGraph setup mode) = some event)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    (message.id, true) ∈ control.execution.receipts := by
  let app := serviceApplication setup mode deadline leaks
  have facts := legalFacts setup leaks _ _ control trace
  have issued := facts.provenance.inputs message emitted
  obtain ⟨entry, entryMember, material, transmission, entryEmitted, state, known, packet⟩ := issued
  have fresh := conform message.sender entry entryMember material message transmission
    entryEmitted
  obtain ⟨freshEvent, freshNamed, readyView, owned⟩ :=
    (serviceRuntime setup mode deadline).freshServiceEnvelope_owned _ message fresh
  rw [named] at freshNamed
  cases Option.some.inj freshNamed
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp entryMember
  have call : FreshCall setup leaks message.sender event (fun _ => 0) entry message :=
    { fresh := ⟨material, transmission⟩
      emitted := entryEmitted
      authored := rfl
      addressed := named
      ready := readyView
      fits := fresh_fits _ message event named fresh
      conforming := EventGraphRuntime.freshServiceEnvelope.acceptable
          (serviceRuntime setup mode deadline) fresh }
  have entryEvent : (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some
      event := by
    rw [submittedEvent_of_issued transmission packet]
    exact named
  have sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other event message.id := by
    intro other otherMember ⟨otherEnvelope, emittedOther, otherAuthor, otherAddressed,
      differentId⟩
    have otherRecall : other ∈ control.execution.recall message.sender := by
      rw [split]
      rcases List.mem_append.mp otherMember with inside | inside
      · exact List.mem_append_left _ inside
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ inside)
    have output : otherEnvelope ∈ app.outputs (control.execution.recall message.sender) :=
      List.mem_filterMap.mpr ⟨other, otherRecall, emittedOther⟩
    rw [← facts.inputs message.sender] at output
    have envelopeMember := (List.mem_filter.mp output).1
    obtain ⟨issuer, issuerMember, _, issuerTransmission, issuerEmitted, _, _, issuerPacket⟩ :=
      facts.provenance.inputs otherEnvelope envelopeMember
    rw [otherAuthor] at issuerMember
    have issuerEvent : (serviceRuntime setup mode deadline).submittedEvent? leaks issuer.action =
        some event := by
      rw [submittedEvent_of_issued issuerTransmission issuerPacket]
      exact otherAddressed
    exact differentId (once message.sender issuer issuerMember entry entryMember event _ _
      issuerEvent entryEvent issuerEmitted entryEmitted)
  have settles : SettlesFreshCalls setup leaks message.sender event (fun _ => 0)
      control.execution :=
    settlesFreshCalls_history setup leaks inclusion message.sender event owned trace
  exact (settles earlier entry later message split call sole).1 completed

end Content

section Retained

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- What retained play keeps at every history: each fresh call conformed on the
view its author saw, each player submitted once per event, and every emitted
packet is good. -/
structure RetainedFacts (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop where
  conform : ∀ who, FreshCallsConform setup leaks execution who
  once : ∀ who, OneCallPerEvent setup leaks execution who
  good : ∀ message, Emitted setup leaks execution message →
    SettledGood setup leaks execution message

variable {setup leaks}

/-- A response keeps a packet good: it changes no contract state or receipt. -/
theorem SettledGood.respond {execution : (serviceApplication setup mode deadline leaks).Execution}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (good : SettledGood setup leaks execution message) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action) :
    SettledGood setup leaks
        (execution.respond (serviceApplication setup mode deadline leaks) who action) message := by
  obtain ⟨configEq, publicEq⟩ := (serviceRuntime setup mode deadline).reactive_respond_application
      leaks execution who action
  have receiptsEq := (serviceApplication setup mode deadline leaks).respond_receipts execution
      who action
  obtain ⟨event, named, ⟨ready, unaccepted, pending⟩ | ⟨accepted, completed, content⟩⟩ := good
  · refine ⟨event, named, Or.inl ⟨configEq ▸ ready, receiptsEq ▸ unaccepted, ?_⟩⟩
    exact pendingContent_congr (congrArg PublicView.observation publicEq) pending
  · refine ⟨event, named, Or.inr ⟨receiptsEq ▸ accepted, configEq ▸ completed, ?_⟩⟩
    unfold settledRecord at content ⊢
    rw [publicEq, receiptsEq]
    exact content

/-- A scheduler command keeps a retained packet good. -/
theorem SettledGood.environment {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler (fun _ => 0))
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
    (facts : SettledFacts setup leaks execution)
    (reached : next ∈
        (execution.environmentStep (serviceApplication setup mode deadline leaks) command).support)
    {remaining : Nat}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace
        (some ⟨remaining, command.actor? (serviceApplication setup mode deadline leaks), next⟩))
    (conform : ∀ who, FreshCallsConform setup leaks next who)
    (once : ∀ who, OneCallPerEvent setup leaks next who)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message)
    (owned : ∀ event, message.payload.call.event? (serviceGraph setup mode) = some event →
      (serviceGraph setup mode).actor? event = some message.sender)
    (good : SettledGood setup leaks execution message) :
    SettledGood setup leaks next message := by
  obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
  have nextEmitted : Emitted setup leaks next message := by
    unfold Emitted at emitted ⊢
    rw [inputsEq]
    exact emitted
  have step := contractStep_environment (serviceRuntime setup mode deadline) leaks execution next
      command reached
  have prefixOf := (serviceApplication setup mode deadline leaks).environmentStep_receipts_prefix
      execution next command reached
  obtain ⟨event, named, ⟨ready, unaccepted, pending⟩ | ⟨accepted, completed, content⟩⟩ := good
  · rcases step with ⟨configEq, _, _, _⟩ | ⟨other, otherReady, action, member⟩
    · by_cases acceptedNow : (message.id, true) ∈ next.receipts
      · obtain ⟨after, handled, applicationEq⟩ :=
          newly_accepted facts reached emitted unaccepted acceptedNow
        obtain ⟨_, acceptedEvent, acceptedNamed, _, acceptedCompleted, _⟩ :=
          accepted_inclusion execution.application after message handled
        rw [named] at acceptedNamed
        cases Option.some.inj acceptedNamed
        rw [← applicationEq, configEq] at acceptedCompleted
        exact (ready.1 acceptedCompleted).elim
      · have observationEq : next.application.publicView.observation =
            execution.application.publicView.observation := by
          change (serviceGraph setup mode).publicObserve next.application.config =
            (serviceGraph setup mode).publicObserve execution.application.config
          rw [configEq]
        exact ⟨event, named, Or.inl ⟨configEq ▸ ready, acceptedNow,
          pendingContent_congr observationEq pending⟩⟩
    · by_cases same : other = event
      swap
      · refine ⟨event, named, Or.inl ⟨?_, fun acceptedNow => ?_, ?_⟩⟩
        · rw [execution.application.config.step_cut other otherReady action _ member]
          exact ready.after_complete otherReady (Ne.symm same)
        · obtain ⟨after, handled, applicationEq⟩ :=
            newly_accepted facts reached emitted unaccepted acceptedNow
          obtain ⟨_, acceptedEvent, acceptedNamed, _, acceptedCompleted, _⟩ :=
            accepted_inclusion execution.application after message handled
          rw [named] at acceptedNamed
          cases Option.some.inj acceptedNamed
          rw [← applicationEq, execution.application.config.step_cut other otherReady action _
            member, EventOrder.Cut.mem_complete] at acceptedCompleted
          rcases acceptedCompleted with equal | old
          · exact same equal.symm
          · exact ready.1 old
        · exact pendingContent_of_other_step named (owned event named) ready otherReady same
            member pending
      have reversed : event = other := same.symm
      subst reversed
      have completedNext : event ∈ next.application.config.cut.completed := by
        rw [execution.application.config.step_cut event otherReady action
          next.application.config member]
        exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
      have acceptedNow := retained_accepted inclusion trace conform once message nextEmitted event
        named completedNext
      obtain ⟨after, handled, applicationEq⟩ :=
        newly_accepted facts reached emitted unaccepted acceptedNow
      obtain ⟨stepEvent, stepNamed, stepReady, stepAction, stepMember⟩ := handle_config_mem_step
        (serviceRuntime setup mode deadline) execution.application after _
        (reactiveHandle_call handled)
      have sameEvent : stepEvent = event := Option.some.inj (stepNamed.symm.trans named)
      subst stepEvent
      refine ⟨event, named, Or.inr ⟨acceptedNow, completedNext, ?_⟩⟩
      unfold settledRecord
      rw [applicationEq]
      exact settledContent_of_pending execution.application after next.receipts message event
        named stepReady stepAction stepMember pending
  · refine ⟨event, named, Or.inr ⟨prefixOf.subset accepted, step.completed_mono completed, ?_⟩⟩
    exact settledContent_step step execution.receipts next.receipts message event named
      completed content
end Retained

end Vegas
