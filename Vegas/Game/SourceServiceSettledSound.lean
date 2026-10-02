/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceSettledEvidence
import Vegas.Game.SourceServiceTrafficSound
import Vegas.Game.SourceServiceCanonicalSerial

/-! # The settled record permits every retained packet

At every history of the retained source service, every transmitted packet is
permitted by the settled record: its event is unsettled, or the contract
accepted it with the content the record checks
(`Vegas.sourceService_history_settled`).

Each retained packet conforms on the view its author saw, so it is on track:
its event is ready, it is not yet accepted, and the record will accept its
content, which stays fixed while the event is ready. The roster calendar
includes an owner's sole packet before the event can complete in any other way
(`Vegas.prescribed_packet_settles` under `Vegas.rosterScheduler_protectedInclusion`),
so the event completes only by accepting it.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Content

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The content a packet will settle with if accepted at this state is what the
record accepts. -/
def PendingContent (state : EventGraphRuntime.State (graph setup))
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  match message.payload.call with
  | .commitment _ candidate =>
      message.payload.evidence = none ∧
        candidate = (message.sender, .prepared (state.publicView.bindingCount message.sender))
  | .opening _ _ _ =>
      certifiedOpening message.payload = true ∧
        state.publicView.openingGuardsAccepted message.payload = true
  | .withhold _ | .malformed _ => False

/-- A retained packet is on track, or accepted with the content the record
accepts. -/
def SettledGood (execution : (application setup leaks).Execution)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  ∃ event, message.payload.call.event? (graph setup) = some event ∧
    ((execution.application.config.cut.Ready event ∧ (message.id, true) ∉ execution.receipts ∧
        PendingContent setup execution.application message) ∨
      ((message.id, true) ∈ execution.receipts ∧
        event ∈ execution.application.config.cut.completed ∧
        ((runtime setup).settledRecord leaks execution).SettledContent message))

variable {setup leaks}

/-- A conforming packet's content is what the record accepts. -/
theorem pendingContent_of_fresh (state : EventGraphRuntime.State (graph setup))
    (message : Message Player (WitnessedPacket (graph setup)))
    (fresh : (runtime setup).freshServiceEnvelope state.publicView message) :
    PendingContent setup state message := by
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | commitment event candidate =>
      obtain ⟨_, canonical, empty, _⟩ := ((runtime setup).freshServiceEnvelope_binding_iff
        state.publicView id event candidate evidence token).mp fresh
      exact ⟨empty, canonical⟩
  | opening event candidate raw =>
      unfold EventGraphRuntime.freshServiceEnvelope at fresh
      exact ⟨fresh.2.2.1, fresh.2.2.2.1⟩
  | withhold event => exact fresh.elim
  | malformed raw => exact fresh.elim

/-- The settled content of a packet for a completed event survives every later
contract step. -/
theorem settledContent_step {before after : EventGraphRuntime.State (graph setup)}
    (step : ContractStep before after)
    (beforeReceipts afterReceipts : List (MessageId Player × Bool))
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (named : message.payload.call.event? (graph setup) = some event)
    (completed : event ∈ before.config.cut.completed)
    (content : (⟨before.publicView, beforeReceipts⟩ : SettledRecord (graph setup)).SettledContent
      message) :
    (⟨after.publicView, afterReceipts⟩ : SettledRecord (graph setup)).SettledContent message := by
  obtain ⟨rest, extended⟩ := step.order_extends
  have member : event ∈ before.publicView.observation.completionOrder :=
    (before.config.history_exact event).mpr completed
  have guardsEq := State.openingGuardsAccepted_congr before after message.payload event named
    (fun predecessor inside => before.config.cut.predecessor_closed completed inside)
    (fun field value stored => step.store_retained field value stored)
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | malformed raw => exact content.elim
  | withhold actual => exact content.elim
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
theorem settledContent_of_pending (before after : EventGraphRuntime.State (graph setup))
    (receipts : List (MessageId Player × Bool))
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (named : message.payload.call.event? (graph setup) = some event)
    (ready : before.config.cut.Ready event) (action : (graph setup).Action event)
    (member : after.config ∈ (before.config.step event ready action).support)
    (pending : PendingContent setup before message) :
    (⟨after.publicView, receipts⟩ : SettledRecord (graph setup)).SettledContent message := by
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
  | withhold actual => exact pending.elim
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
theorem SettledGood.permits {execution : (application setup leaks).Execution}
    {message : Message Player (WitnessedPacket (graph setup))}
    (good : SettledGood setup leaks execution message) :
    ((runtime setup).settledRecord leaks execution).permits message = true := by
  obtain ⟨event, named, ⟨ready, _, _⟩ | ⟨accepted, _, content⟩⟩ := good
  · exact SettledRecord.permits_of_unsettled _ message event named fun inside =>
      ready.1 ((execution.application.config.history_exact event).mp inside)
  · exact SettledRecord.permits_of_accepted _ message event named accepted content

/-- Pending content reads only the public observation. -/
theorem pendingContent_congr {first second : EventGraphRuntime.State (graph setup)}
    (same : second.publicView.observation = first.publicView.observation)
    {message : Message Player (WitnessedPacket (graph setup))}
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
  | withhold event => simp only [call] at pending
  | malformed raw => simp only [call] at pending

/-- A conforming packet meets the inclusion deadline with no slack. -/
theorem fresh_fits (view : PublicView (graph setup))
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (named : message.payload.call.event? (graph setup) = some event)
    (fresh : (runtime setup).freshServiceEnvelope view message) :
    view.InclusionFitsDeadline (runtime setup) (fun _ => 0) event := by
  have deadline : match view.activatedAt event with
      | none => False
      | some entered => view.clock - entered < (runtime setup).deadline event := by
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
    | withhold actual => exact fresh.elim
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
theorem submittedEvent_of_issued {entry : (application setup leaks).PlayerEntry}
    {material : (application setup leaks).Submission}
    (transmission : entry.action.transmission = some material)
    {state : EventGraphRuntime.State (graph setup)} {who : Player}
    {known : List (Message Player (WitnessedPacket (graph setup)))}
    {message : Message Player (WitnessedPacket (graph setup))}
    (packet : (application setup leaks).packet state who known material = message.payload) :
    (runtime setup).submittedEvent? leaks entry.action =
      message.payload.call.event? (graph setup) := by
  unfold EventGraphRuntime.submittedEvent?
  rw [transmission, ← packet]
  rfl

/-- **Retained packets settle.** Under a scheduler that includes an owner's sole
packet before its event can complete in any other way, when every fresh call
conforms on the view its author saw and each player submits once per event, the
event of every emitted packet completes only by accepting that packet. -/
theorem retained_accepted {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      (fun _ => 0))
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (conform : ∀ who, FreshCallsConform setup leaks control.execution who)
    (once : ∀ who, OneCallPerEvent setup leaks control.execution who)
    (message : Message Player (WitnessedPacket (graph setup)))
    (emitted : Emitted setup leaks control.execution message) (event : (graph setup).EventId)
    (named : message.payload.call.event? (graph setup) = some event)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    (message.id, true) ∈ control.execution.receipts := by
  let app := application setup leaks
  have facts := legalFacts setup leaks _ _ control trace
  have issued := facts.provenance.inputs message emitted
  obtain ⟨entry, entryMember, material, transmission, entryEmitted, state, known, packet⟩ := issued
  have fresh := conform message.sender entry entryMember material message transmission
    entryEmitted
  obtain ⟨freshEvent, freshNamed, readyView, owned⟩ :=
    (runtime setup).freshServiceEnvelope_owned _ message fresh
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
      conforming := EventGraphRuntime.freshServiceEnvelope.acceptable (runtime setup) fresh }
  have entryEvent : (runtime setup).submittedEvent? leaks entry.action = some event := by
    rw [submittedEvent_of_issued transmission packet]
    exact named
  have sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id := by
    intro other otherMember ⟨replayed, emittedOther, replayedAuthor, replayedAddressed,
      differentId⟩
    have otherRecall : other ∈ control.execution.recall message.sender := by
      rw [split]
      rcases List.mem_append.mp otherMember with inside | inside
      · exact List.mem_append_left _ inside
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ inside)
    have output : replayed ∈ app.outputs (control.execution.recall message.sender) :=
      List.mem_filterMap.mpr ⟨other, otherRecall, emittedOther⟩
    rw [← facts.inputs message.sender] at output
    have replayMember := (List.mem_filter.mp output).1
    obtain ⟨issuer, issuerMember, _, issuerTransmission, issuerEmitted, _, _, issuerPacket⟩ :=
      facts.provenance.inputs replayed replayMember
    rw [replayedAuthor] at issuerMember
    have issuerEvent : (runtime setup).submittedEvent? leaks issuer.action = some event := by
      rw [submittedEvent_of_issued issuerTransmission issuerPacket]
      exact replayedAddressed
    exact differentId (once message.sender issuer issuerMember entry entryMember event _ _
      issuerEvent entryEvent issuerEmitted entryEmitted)
  have settles : SettlesFreshCalls setup leaks message.sender event (fun _ => 0)
      control.execution :=
    settlesFreshCalls_history setup leaks inclusion message.sender event owned trace
  exact (settles earlier entry later message split call sole).1 completed

end Content

section Retained

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- What retained play keeps at every history: each fresh call conformed on the
view its author saw, each player submitted once per event, and every emitted
packet is good. -/
structure RetainedFacts (execution : (application setup leaks).Execution) : Prop where
  conform : ∀ who, FreshCallsConform setup leaks execution who
  once : ∀ who, OneCallPerEvent setup leaks execution who
  good : ∀ message, Emitted setup leaks execution message →
    SettledGood setup leaks execution message

variable {setup leaks}

theorem retainedFacts_initial (state : (application setup leaks).State) :
    RetainedFacts setup leaks (ReactiveApplication.Execution.initial (application setup leaks)
      state) where
  conform who entry member := by
    simp [ReactiveApplication.Execution.initial] at member
  once who first member := by
    simp [ReactiveApplication.Execution.initial] at member
  good message emitted := by
    simp [Emitted, ReactiveApplication.Execution.initial, MessageNetwork.empty] at emitted

/-- A response keeps a packet good: it changes no contract state or receipt. -/
theorem SettledGood.respond {execution : (application setup leaks).Execution}
    {message : Message Player (WitnessedPacket (graph setup))}
    (good : SettledGood setup leaks execution message) (who : Player)
    (action : (application setup leaks).Action) :
    SettledGood setup leaks (execution.respond (application setup leaks) who action) message := by
  obtain ⟨configEq, publicEq⟩ := (runtime setup).reactive_respond_application leaks execution
    who action
  have receiptsEq := (application setup leaks).respond_receipts execution who action
  obtain ⟨event, named, ⟨ready, unaccepted, pending⟩ | ⟨accepted, completed, content⟩⟩ := good
  · refine ⟨event, named, Or.inl ⟨configEq ▸ ready, receiptsEq ▸ unaccepted, ?_⟩⟩
    exact pendingContent_congr (congrArg PublicView.observation publicEq) pending
  · refine ⟨event, named, Or.inr ⟨receiptsEq ▸ accepted, configEq ▸ completed, ?_⟩⟩
    unfold settledRecord at content ⊢
    rw [publicEq, receiptsEq]
    exact content

/-- A scheduler command keeps a retained packet good. -/
theorem SettledGood.environment {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      (fun _ => 0))
    {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command} (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {remaining : Nat}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, command.actor? (application setup leaks), next⟩))
    (conform : ∀ who, FreshCallsConform setup leaks next who)
    (once : ∀ who, OneCallPerEvent setup leaks next who)
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks execution message)
    (good : SettledGood setup leaks execution message) :
    SettledGood setup leaks next message := by
  obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
  have nextEmitted : Emitted setup leaks next message := by
    unfold Emitted at emitted ⊢
    rw [inputsEq]
    exact emitted
  have step := contractStep_environment (runtime setup) leaks execution next command reached
  have prefixOf := (application setup leaks).environmentStep_receipts_prefix execution next
    command reached
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
          change (graph setup).publicObserve next.application.config =
            (graph setup).publicObserve execution.application.config
          rw [configEq]
        exact ⟨event, named, Or.inl ⟨configEq ▸ ready, acceptedNow,
          pendingContent_congr observationEq pending⟩⟩
    · cases ready_unique _ otherReady ready
      have completedNext : event ∈ next.application.config.cut.completed := by
        rw [execution.application.config.step_cut event otherReady action
          next.application.config member]
        exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
      have acceptedNow := retained_accepted inclusion trace conform once message nextEmitted event
        named completedNext
      obtain ⟨after, handled, applicationEq⟩ :=
        newly_accepted facts reached emitted unaccepted acceptedNow
      obtain ⟨stepEvent, stepNamed, stepReady, stepAction, stepMember⟩ := handle_config_mem_step
        (runtime setup) execution.application after _ (reactiveHandle_call handled)
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

/-- A response that keeps the recall of every other player and appends one
entry to the responder's. -/
theorem respond_recall_cases (execution : (application setup leaks).Execution) (who : Player)
    (action : (application setup leaks).Action) (observer : Player)
    (entry : (application setup leaks).PlayerEntry)
    (member : entry ∈ (execution.respond (application setup leaks) who action).recall observer) :
    entry ∈ execution.recall observer ∨
      (observer = who ∧ entry.beforeView = execution.observe (application setup leaks) who ∧
        entry.action = action ∧
        ∀ material, action.transmission = some material →
          entry.emitted = some ⟨(who, execution.network.nextSerial who),
            (application setup leaks).packet ((application setup leaks).submit
              execution.application who material) who (execution.network.known who) material⟩) := by
  by_cases same : observer = who
  · subst observer
    rcases action with ⟨transmission⟩
    cases transmission with
    | none =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
          List.mem_singleton] at member
        rcases member with prior | fresh
        · exact Or.inl prior
        · subst fresh
          exact Or.inr ⟨rfl, rfl, rfl, fun material submitted => by cases submitted⟩
    | some material =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
          List.mem_singleton] at member
        rcases member with prior | fresh
        · exact Or.inl prior
        · subst fresh
          refine Or.inr ⟨rfl, rfl, rfl, fun other submitted => ?_⟩
          cases submitted
          rfl
  · left
    have recallEq := (application setup leaks).respond_recall_other execution who observer same
      action
    rw [recallEq] at member
    exact member

/-- A first submission names an event no earlier own entry submitted for. -/
theorem unrecorded_of_firstSubmission (past : List (application setup leaks).PlayerEntry)
    (response : (application setup leaks).Action) (event : (graph setup).EventId)
    (first : (runtime setup).firstSubmission leaks past response = true)
    (submitted : (runtime setup).submittedEvent? leaks response = some event) :
    ∀ entry ∈ past, (runtime setup).submittedEvent? leaks entry.action ≠ some event := by
  intro entry member recorded
  have found : (runtime setup).eventRecorded leaks past event = true :=
    List.any_eq_true.mpr ⟨entry, member, decide_eq_true recorded⟩
  rw [(runtime setup).firstSubmission_false_of_recorded leaks past event found response
    submitted] at first
  cases first

/-- **Retained play keeps its facts.** Under a scheduler with protected
inclusion, a response menu whose fresh submissions conform on the current
public view and submit once per event keeps the retained facts at every
history. -/
theorem retainedFacts_history {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      (fun _ => 0))
    (menu : (application setup leaks).ResponseMenu)
    (fresh : ∀ {remaining who execution},
      (menu.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, some who, execution⟩) →
      ∀ response ∈ menu.actions who (execution.recall who)
        (execution.observe (application setup leaks) who),
      ∀ material, response.transmission = some material →
        (runtime setup).freshServiceEnvelope execution.application.publicView
          ⟨(who, execution.network.nextSerial who),
            (application setup leaks).packet ((application setup leaks).submit
              execution.application who material) who (execution.network.known who) material⟩)
    (first : ∀ who past view response, response ∈ menu.actions who past view →
      (runtime setup).firstSubmission leaks past response = true) :
    ∀ {state} (_ : (menu.protocol (initialLaw setup) horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (RetainedFacts setup leaks) state
  | _, .start => trivial
  | _, .extend (source := before) prior joint legal reached => by
      let app := application setup leaks
      have valid := retainedFacts_history inclusion menu fresh first prior
      have rawPrior := menu.toRawTrace (initialLaw setup) horizon scheduler prior
      have rawNext := menu.toRawTrace (initialLaw setup) horizon scheduler
        (.extend prior joint legal reached)
      cases before with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact retainedFacts_initial state
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          change RetainedFacts setup leaks execution at valid
          have facts := settledFacts_history (initialLaw setup) _ _ rawPrior
          cases actor with
          | some who =>
              obtain ⟨response, choice, member⟩ : ∃ response, joint who = some response ∧
                  response ∈ menu.actions who (execution.recall who)
                    (execution.observe app who) := by
                have legalChoice := legal.2 who
                cases chosen : joint who with
                | none =>
                    rw [chosen] at legalChoice
                    exact (legalChoice rfl).elim
                | some response =>
                    rw [chosen] at legalChoice
                    exact ⟨response, rfl, legalChoice.2⟩
              have freshNew := fresh prior response member
              cases (PMF.mem_support_pure_iff _ _).mp reached
              simp only [choice, Option.getD_some]
              change RetainedFacts setup leaks (execution.respond app who response)
              have firstSubmitted := first who _ _ response member
              obtain ⟨configEq, publicEq⟩ := (runtime setup).reactive_respond_application leaks
                execution who response
              refine ⟨fun observer entry entryMember material message transmission emitted => ?_,
                fun observer => ?_, fun message emitted => ?_⟩
              · rcases respond_recall_cases execution who response observer entry entryMember with
                  prior | ⟨_, viewEq, actionEq, emittedEq⟩
                · exact valid.conform observer entry prior material message transmission emitted
                · rw [actionEq] at transmission
                  rw [emittedEq material transmission] at emitted
                  cases Option.some.inj emitted
                  rw [viewEq]
                  exact freshNew material transmission
              · intro first firstMember second secondMember event firstMessage secondMessage
                  firstEvent secondEvent firstEmitted secondEmitted
                have submittedOf : ∀ entry : app.PlayerEntry,
                    (runtime setup).submittedEvent? leaks entry.action = some event →
                    ∃ material, entry.action.transmission = some material := by
                  intro entry submitted
                  rcases entry with ⟨view, ⟨transmission⟩, emittedOption⟩
                  rcases transmission with _ | material
                  · cases submitted
                  · exact ⟨material, rfl⟩
                rcases respond_recall_cases execution who response observer first firstMember with
                    firstPrior | ⟨firstWho, _, firstAction, firstEmittedEq⟩ <;>
                  rcases respond_recall_cases execution who response observer second secondMember
                    with secondPrior | ⟨secondWho, _, secondAction, secondEmittedEq⟩
                · exact valid.once observer first firstPrior second secondPrior event firstMessage
                    secondMessage firstEvent secondEvent firstEmitted secondEmitted
                · subst secondWho
                  rw [secondAction] at secondEvent
                  exact (unrecorded_of_firstSubmission _ response event firstSubmitted
                    secondEvent first firstPrior firstEvent).elim
                · subst firstWho
                  rw [firstAction] at firstEvent
                  exact (unrecorded_of_firstSubmission _ response event firstSubmitted
                    firstEvent second secondPrior secondEvent).elim
                · obtain ⟨material, submitted⟩ := submittedOf first firstEvent
                  rw [firstAction] at submitted
                  rw [firstEmittedEq material submitted] at firstEmitted
                  rw [secondEmittedEq material submitted] at secondEmitted
                  rw [← Option.some.inj firstEmitted, ← Option.some.inj secondEmitted]
              · rcases respond_emitted facts who response message emitted with prior |
                    ⟨material, submitted, rfl⟩
                · exact (valid.good message prior).respond who response
                · have fresh := freshNew material submitted
                  obtain ⟨event, named, readyView⟩ :=
                    (runtime setup).freshServiceEnvelope_ready _ _ fresh
                  refine ⟨event, named, Or.inl ⟨?_, ?_, ?_⟩⟩
                  · change (execution.respond app who response).application.config.cut.Ready
                      event
                    rw [configEq]
                    exact (execution.application.publicView_eventReady event).mp readyView
                  · rw [app.respond_receipts execution who response]
                    intro accepted
                    obtain ⟨other, otherMember, same⟩ :=
                      List.mem_map.mp (facts.receipt_published accepted)
                    have bound := facts.serials.ledger other otherMember
                    rw [same] at bound
                    exact Nat.lt_irrefl _ bound
                  · exact pendingContent_congr (congrArg PublicView.observation publicEq)
                      (pendingContent_of_fresh execution.application _ fresh)
          | none =>
              cases remaining with
              | zero =>
                  cases (PMF.mem_support_pure_iff _ _).mp reached
                  exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have recallEq := app.environmentStep_recall execution next command supported
                  have conform : ∀ who, FreshCallsConform setup leaks next who := by
                    intro who
                    unfold FreshCallsConform
                    rw [recallEq]
                    exact valid.conform who
                  have once : ∀ who, OneCallPerEvent setup leaks next who := by
                    intro who
                    unfold OneCallPerEvent
                    rw [recallEq]
                    exact valid.once who
                  obtain ⟨inputsEq, _, _⟩ :=
                    environmentStep_shape setup leaks execution next command supported
                  refine ⟨conform, once, fun message emitted => ?_⟩
                  have emittedBefore : Emitted setup leaks execution message := by
                    unfold Emitted at emitted ⊢
                    rw [← inputsEq]
                    exact emitted
                  exact (valid.good message emittedBefore).environment inclusion facts supported
                    rawNext conform once emittedBefore

/-- In the retained source service a fresh submission conforms on the public
view its author sees. -/
theorem sourceService_fresh_response [Fintype Player] (bounds : MessageBounds (graph setup))
    (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {rosters : (graph setup).EventId → List Player}
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks) {remaining : Nat} {who : Player}
    {execution : (application setup leaks).Execution}
    (prior : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (submitted : response.transmission = some material) :
    (runtime setup).freshServiceEnvelope execution.application.publicView
      ⟨(who, execution.network.nextSerial who),
        (application setup leaks).packet ((application setup leaks).submit
          execution.application who material) who (execution.network.known who) material⟩ := by
  classical
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  let joint : ∀ i, Option ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Action i) :=
    fun i => if i = who then some response else none
  have legal : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Legal
        (some ⟨remaining, some who, execution⟩) joint := by
    refine ⟨fun stopped => ?_, fun player => ?_⟩
    · change remaining = 0 ∧ some who = none at stopped
      cases stopped.2
    · by_cases same : player = who
      · subst player
        simp only [joint, ↓reduceIte]
        exact ⟨rfl, member⟩
      · simp only [joint, same, ↓reduceIte]
        intro active
        exact same (Option.some.inj active.symm)
  have reached : some ⟨remaining, none, execution.respond app who response⟩ ∈
      ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).step
          (some ⟨remaining, some who, execution⟩) ⟨joint, legal⟩).support := by
    change _ ∈ (app.transition (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) (some ⟨remaining, some who, execution⟩)
        joint).support
    simp only [ReactiveApplication.transition, joint, ↓reduceIte, Option.getD_some]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have trafficOk := sourceService_history_traffic bounds values capacity opportunities network
    ⟨_, .extend prior joint legal reached⟩
  have traffic := app.stateTraffic_transition (initialLaw setup) _ _
    ⟨_, menu.toRawTrace (initialLaw setup) _ _ prior⟩ joint _ reached
  have facts := settledFacts_history (initialLaw setup) _ _
    (menu.toRawTrace (initialLaw setup) _ _ prior)
  rcases response with ⟨transmission⟩
  cases submitted
  have recorded : (⟨execution.application.publicView, execution.network.ledger,
      ⟨(who, execution.network.nextSerial who),
        app.packet (app.submit execution.application who material) who
          (execution.network.known who) material⟩⟩ : app.TrafficRecord) ∈
      app.stateTraffic (some ⟨remaining, none,
        execution.respond app who ⟨some material⟩⟩) := by
    rw [traffic]
    refine List.mem_append_right _ ?_
    simp only [ReactiveApplication.trafficStep, ReactiveApplication.Execution.respond,
      MessageNetwork.submit, List.drop_left', List.map_cons, List.map_nil,
      List.mem_singleton]
    rfl
  have permitted := trafficOk _ recorded
  have unpublished : (who, execution.network.nextSerial who) ∉
      execution.network.ledger.map Message.id := by
    intro published
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp published
    have bound := facts.serials.ledger other otherMember
    rw [same] at bound
    exact Nat.lt_irrefl _ bound
  exact (((runtime setup).permittedServiceEnvelope_unpublished_iff _ _ _ unpublished).mp
    permitted).2

/-- **The settled record permits every retained packet.** At every history of
the retained source service, including off-path and intermediate histories,
every transmitted packet is permitted by the contract's current record. -/
theorem sourceService_history_settled [Fintype Player] (bounds : MessageBounds (graph setup))
    (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {rosters : (graph setup).EventId → List Player}
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks) {control : (application setup leaks).Control}
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) :
    ∀ record ∈ (application setup leaks).executionTraffic control.execution,
      ((runtime setup).settledRecord leaks control.execution).permits record.envelope =
        true := by
  have retained : RetainedFacts setup leaks control.execution :=
    retainedFacts_history (rosterScheduler_protectedInclusion setup leaks rosters network)
      (sourceServiceMenu setup leaks bounds rosters)
      (fun prior response member material submitted =>
        sourceService_fresh_response bounds values capacity opportunities network prior response
          member material submitted)
      (fun who _ _ response member => bounds.compiledActions_firstSubmission (runtime setup) leaks
        who _ _ response (sourceServiceMenu_in_compiled setup leaks bounds rosters who _ _ member))
      trace
  have inputs := (application setup leaks).stateTraffic_inputs (initialLaw setup) _ _
    ((sourceServiceMenu setup leaks bounds rosters).toRawTrace (initialLaw setup) _ _ trace)
  change ((application setup leaks).executionTraffic control.execution).map
    ReactiveApplication.TrafficRecord.envelope = control.execution.network.inputs at inputs
  intro record member
  have emitted : Emitted setup leaks control.execution record.envelope := by
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  exact (retained.good _ emitted).permits

end Retained

end Vegas
