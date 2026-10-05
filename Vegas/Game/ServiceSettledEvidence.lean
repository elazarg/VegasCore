/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterAsync
import Vegas.Pending.ReactiveSettledStability
import Vegas.Pending.ReactiveServiceAudit
import Vegas.Pending.ReactiveFreshCallAcceptance
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveSignedEvidence
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveTrafficContinuation

/-! # Breaches judged at transmission are breaches of the settled record

The continuation-repair proofs classify a deviation by a packet that breaks the
public conformance rule on the view its author saw at transmission
(`Vegas.EventGraphRuntime.permittedServiceEnvelope`). That rule is a proof
device: the audit cannot read send time. This file shows that it never charges
more than the audit does. On the sequentialized graph, at every complete
settlement of every legal history, under arbitrary responses and scheduling,
an author of a transmission that breaks the send-time rule also authored a
packet that the settled record forbids
(`Vegas.settled_breach_of_sendTime_breach`).

Each breach at transmission leaves a mark that later steps cannot remove:

* content that no settlement accepts: a missing or foreign readiness token, no
  event, withholding carrying evidence, opening evidence on a commitment, an opening
  without its exact certificate, or a sender who is not the event's actor;
* a packet never accepted whose event has completed;
* a packet not yet accepted whose event is ready, and which the handler cannot
  accept before the event completes, or whose content the record will reject
  if it does;
* an accepted packet whose content the record rejects;
* two packets of one author for one event, of which the contract accepts at
  most one.

A wrong serial at transmission is the last kind or the second: an earlier
identifier of the author is still unpublished, or a later one is already on
the ledger, and on the sequentialized graph the event of either is the one
ready event or has completed without it.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Handle

variable {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)

/-- An accepted packet is authored by its event's actor. -/
theorem handle_sender_actor (state next : EventGraphRuntime.State graph)
    (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) (event : graph.EventId)
    (named : Payload.event? graph message.payload = some event) :
    graph.actor? event = some message.sender := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              by_cases sender : id.1 = owner
              · exact (nodeView_bind_actor outputEq codeEq).trans (congrArg some sender.symm)
              · simp [handle, ready, timely, view, Message.sender, sender] at accepted
          | resolve owner payload binding checks outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | opening actual candidate raw =>
      change some actual = some event at named
      cases Option.some.inj named
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              by_cases sender : id.1 = owner
              · exact (nodeView_resolve_actor outputEq codeEq).trans (congrArg some sender.symm)
              · simp [handle, ready, timely, view, Message.sender, sender] at accepted
          | bind owner payload outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | withhold actual =>
      change some actual = some event at named
      cases Option.some.inj named
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              by_cases sender : id.1 = owner
              · exact (nodeView_resolve_actor outputEq codeEq).trans (congrArg some sender.symm)
              · simp [handle, ready, timely, view, Message.sender, sender] at accepted
          | bind owner payload outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted

end Handle

section ContractStep

variable {graph : Vegas.EventGraph Player L}

/-- One scheduler command completes at most one event; otherwise it changes no
completion, accepted handle or activation time, and the clock only advances. -/
def ContractStep (before after : EventGraphRuntime.State graph) : Prop :=
  (after.config = before.config ∧ after.accepted = before.accepted ∧
      after.activatedAt = before.activatedAt ∧ before.clock ≤ after.clock) ∨
    ∃ event, ∃ (ready : before.config.cut.Ready event) (action : graph.Action event),
      after.config ∈ (before.config.step event ready action).support

omit [DecidableEq Player] in
theorem ContractStep.refl (state : EventGraphRuntime.State graph) : ContractStep state state :=
  Or.inl ⟨rfl, rfl, rfl, le_refl _⟩

theorem contractStep_environment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    ContractStep execution.application next.application := by
  unfold ReactiveApplication.Execution.environmentStep at reached
  rw [PMF.support_map] at reached
  obtain ⟨updated, supported, rfl⟩ := reached
  cases command with
  | activate who =>
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact ContractStep.refl _
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ContractStep.refl _
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change ContractStep execution.application
        (execution.includePending (runtime.reactiveApplication leaks) id).application
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact ContractStep.refl _
      | some message =>
          change ContractStep execution.application
            (((runtime.reactiveApplication leaks).handle execution.application message).getD
              execution.application)
          cases accepted : (runtime.reactiveApplication leaks).handle execution.application
              message with
          | none => exact ContractStep.refl _
          | some after =>
              obtain ⟨event, _, ready, action, member⟩ := handle_config_mem_step runtime
                execution.application after _ (reactiveHandle_call accepted)
              exact Or.inr ⟨event, ready, action, member⟩
  | application command =>
      rw [PMF.support_map] at supported
      obtain ⟨state, member, rfl⟩ := supported
      replace member : state ∈ (EventGraphRuntime.environmentStep runtime
        (execution.application : EventGraphRuntime.State graph) command).support := member
      change ContractStep (execution.application : EventGraphRuntime.State graph) state
      have acceptedEq := (environmentStep_tables runtime execution.application state command
        member).1
      cases command with
      | advanceClock =>
          simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
          subst state
          exact Or.inl ⟨rfl, rfl, rfl, Nat.le_succ _⟩
      | executeSample event =>
          obtain ⟨clockEq, effect⟩ := environmentStep_executeSample_config_activated runtime
            execution.application state event member
          rcases effect with ⟨configEq, activatedEq⟩ | ⟨ready, action, configMem, _⟩
          · exact Or.inl ⟨configEq, acceptedEq, activatedEq, clockEq.symm ▸ le_refl _⟩
          · exact Or.inr ⟨event, ready, action, configMem⟩
      | expire event =>
          obtain ⟨clockEq, effect⟩ := environmentStep_expire_config_activated runtime
            execution.application state event member
          rcases effect with ⟨configEq, activatedEq⟩ | ⟨ready, action, configMem, _⟩
          · exact Or.inl ⟨configEq, acceptedEq, activatedEq, clockEq.symm ▸ le_refl _⟩
          · exact Or.inr ⟨event, ready, action, configMem⟩

omit [DecidableEq Player] in
/-- Completed events stay completed. -/
theorem ContractStep.completed_mono {before after : EventGraphRuntime.State graph}
    (step : ContractStep before after) {event : graph.EventId}
    (completed : event ∈ before.config.cut.completed) :
    event ∈ after.config.cut.completed := by
  rcases step with ⟨configEq, _⟩ | ⟨other, ready, action, member⟩
  · rw [configEq]
    exact completed
  · rw [before.config.step_cut other ready action after.config member]
    exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inr completed)

omit [DecidableEq Player] in
/-- Available fields keep their values. -/
theorem ContractStep.store_retained {before after : EventGraphRuntime.State graph}
    (step : ContractStep before after) (field : graph.Field)
    (value : (graph.layout field).Value) (stored : before.config.store field = some value) :
    after.config.store field = some value := by
  rcases step with ⟨configEq, _⟩ | ⟨other, ready, action, member⟩
  · rw [configEq]
    exact stored
  · exact before.config.step_store_of_some after.config other ready action member field value
      stored

omit [DecidableEq Player] in
/-- The completion order only grows at its end. -/
theorem ContractStep.order_extends {before after : EventGraphRuntime.State graph}
    (step : ContractStep before after) :
    ∃ rest, after.publicView.observation.completionOrder =
      before.publicView.observation.completionOrder ++ rest := by
  rcases step with ⟨configEq, _⟩ | ⟨other, ready, action, member⟩
  · refine ⟨[], ?_⟩
    change after.config.history.map Completion.event = _
    rw [configEq, List.append_nil]
    rfl
  · refine ⟨[other], ?_⟩
    change after.config.history.map Completion.event =
      before.config.history.map Completion.event ++ [other]
    rw [before.config.step_history other ready action after.config member]
    simp

end ContractStep

section Facts

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- An envelope the network has carried as an input. -/
def Emitted (execution : (application setup leaks).Execution)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  message ∈ execution.network.inputs

/-- One scheduler command keeps the inputs and the next serials. It either keeps
the ledger and receipts and lets the network only learn, or includes one pending
envelope with its receipt. -/
theorem environmentStep_shape (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    next.network.inputs = execution.network.inputs ∧
      next.network.nextSerial = execution.network.nextSerial ∧
      ((next.receipts = execution.receipts ∧ next.network.ledger = execution.network.ledger ∧
          ∀ safe : Message Player (WitnessedPacket (graph setup)) → Prop,
            execution.network.Satisfies safe → next.network.Satisfies safe) ∨
        ∃ id message, execution.network.lookup id = some message ∧
          next.network = (execution.network.includePending id).2 ∧
          next.receipts = execution.receipts ++
            [(id, ((application setup leaks).handle execution.application message).isSome)] ∧
          next.application = ((application setup leaks).handle execution.application
            message).getD execution.application) := by
  unfold ReactiveApplication.Execution.environmentStep at reached
  rw [PMF.support_map] at reached
  obtain ⟨updated, supported, rfl⟩ := reached
  cases command with
  | activate who =>
      rw [PMF.support_map] at supported
      obtain ⟨selected, _, rfl⟩ := supported
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid.learn who selected⟩⟩
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid⟩⟩
  | application command =>
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid⟩⟩
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (execution.includePending (application setup leaks) id).network.inputs = _ ∧
        (execution.includePending (application setup leaks) id).network.nextSerial = _ ∧
        (((execution.includePending (application setup leaks) id).receipts = _ ∧
          (execution.includePending (application setup leaks) id).network.ledger = _ ∧ _) ∨ _)
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid⟩⟩
      | some message =>
          refine ⟨rfl, rfl, Or.inr ⟨id, message, found, ?_, rfl, rfl⟩⟩
          simp only [found]

/-- The facts every legal history keeps, for every scheduler and arbitrary
responses, that tie the receipts and tokens to the traffic. -/
structure SettledFacts (execution : (application setup leaks).Execution) : Prop where
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  receipts : execution.ReceiptsSound (application setup leaks) (fun _ => True)
  /-- Every envelope the network holds was an input. -/
  carried : execution.network.Satisfies (Emitted setup leaks execution)
  /-- Every allocated identifier was emitted. -/
  allocated : ∀ who serial, serial < execution.network.nextSerial who →
    ∃ message, Emitted setup leaks execution message ∧ message.id = (who, serial)
  /-- A readiness token names an event whose prerequisites have completed. -/
  issued : ∀ message, Emitted setup leaks execution message → ∀ token,
    message.payload.token = some token →
    ∀ predecessor ∈ (graph setup).order.predecessors token.event,
      predecessor ∈ execution.application.config.cut.completed
  /-- An accepting receipt names a ledger envelope with a valid token, whose
  event has completed and whose sender is that event's actor. -/
  accepted : ∀ id, (id, true) ∈ execution.receipts →
    ∃ message ∈ execution.network.ledger, message.id = id ∧
      message.payload.tokenValid = true ∧
      ∃ event, message.payload.call.event? (graph setup) = some event ∧
        event ∈ execution.application.config.cut.completed ∧
        (graph setup).actor? event = some message.sender
  /-- The contract accepts at most one identifier per event. -/
  single : ∀ first ∈ execution.network.ledger, ∀ second ∈ execution.network.ledger,
    (first.id, true) ∈ execution.receipts → (second.id, true) ∈ execution.receipts →
    ∀ event, first.payload.call.event? (graph setup) = some event →
      second.payload.call.event? (graph setup) = some event → first.id = second.id
  /-- Once a later identifier of an author is accepted, the event of each of the
  author's earlier identifiers with a valid token has completed. -/
  ordered : ∀ earlier later, Emitted setup leaks execution earlier →
    Emitted setup leaks execution later → earlier.sender = later.sender →
    earlier.id.2 < later.id.2 → (later.id, true) ∈ execution.receipts →
    earlier.payload.tokenValid = true →
    ∀ event, earlier.payload.call.event? (graph setup) = some event →
      event ∈ execution.application.config.cut.completed

variable {setup leaks}

/-- Two ready events of the sequentialized graph are equal. -/
theorem ready_unique (cut : (graph setup).order.Cut) {first second : (graph setup).EventId}
    (firstReady : cut.Ready first) (secondReady : cut.Ready second) : first = second :=
  setup.eventGraph.sequentialize_ready_unique cut firstReady secondReady

/-- A receipt names an identifier on the ledger. -/
theorem SettledFacts.receipt_published {execution : (application setup leaks).Execution}
    (facts : SettledFacts setup leaks execution) {id : MessageId Player} {accepted : Bool}
    (receipt : (id, accepted) ∈ execution.receipts) :
    id ∈ execution.network.ledger.map Message.id := by
  have sound := facts.receipts
  unfold ReactiveApplication.Execution.ReceiptsSound at sound
  generalize execution.network.ledger = ledger at sound ⊢
  generalize execution.receipts = receipts at sound receipt
  induction sound with
  | nil => cases receipt
  | cons head _ ih =>
      rw [List.map_cons]
      rcases List.mem_cons.mp receipt with same | inside
      · subst same
        exact List.mem_cons.mpr (Or.inl head.1)
      · exact List.mem_cons_of_mem _ (ih inside)

/-- Two emitted envelopes with one identifier are equal. -/
theorem SettledFacts.emitted_unique {execution : (application setup leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {first second : Message Player (WitnessedPacket (graph setup))}
    (firstEmitted : Emitted setup leaks execution first)
    (secondEmitted : Emitted setup leaks execution second) (same : first.id = second.id) :
    first = second := by
  exact ((facts.unique.inputs first firstEmitted).inputs second secondEmitted
    same.symm).symm

/-- An emitted envelope's serial is below its author's next serial. -/
theorem SettledFacts.emitted_serial {execution : (application setup leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks execution message) :
    message.id.2 < execution.network.nextSerial message.id.1 := by
  exact facts.serials.inputs message emitted

theorem settledFacts_initial (state : (application setup leaks).State) :
    SettledFacts setup leaks (ReactiveApplication.Execution.initial (application setup leaks)
      state) where
  serials := MessageNetwork.SerialsBeforeNext.empty
  unique := MessageNetwork.UniqueIds.empty
  receipts := (application setup leaks).receiptsSound_initial _ state
  carried := MessageNetwork.Satisfies.empty
  allocated := by
    intro who serial lower
    exact absurd lower (Nat.not_lt_zero _)
  issued := by
    intro message emitted
    simp [Emitted, ReactiveApplication.Execution.initial, MessageNetwork.empty] at emitted
  accepted := by
    intro id member
    simp [ReactiveApplication.Execution.initial] at member
  single := by
    intro first member
    simp [ReactiveApplication.Execution.initial, MessageNetwork.empty] at member
  ordered := by
    intro earlier later emitted
    simp [Emitted, ReactiveApplication.Execution.initial, MessageNetwork.empty] at emitted

/-- A response only appends inputs. -/
theorem respond_emitted_mono (execution : (application setup leaks).Execution) (who : Player)
    (action : (application setup leaks).Action)
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks execution message) :
    Emitted setup leaks (execution.respond (application setup leaks) who action) message := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact emitted
  | some material =>
      unfold Emitted at emitted ⊢
      simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
        List.mem_append]
      exact Or.inl emitted

/-- A response emits fresh at most the responder's next identifier; any other new
input is an envelope the network already carried. -/
theorem respond_emitted {execution : (application setup leaks).Execution}
    (_facts : SettledFacts setup leaks execution) (who : Player)
    (action : (application setup leaks).Action)
    (message : Message Player (WitnessedPacket (graph setup)))
    (emitted : Emitted setup leaks (execution.respond (application setup leaks) who action)
      message) :
    Emitted setup leaks execution message ∨
      ∃ material, action.transmission = some material ∧
        message = ⟨(who, execution.network.nextSerial who),
          (application setup leaks).packet ((application setup leaks).submit
            execution.application who material) who (execution.network.known who) material⟩ := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl emitted
  | some material =>
      unfold Emitted at emitted
      simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
        List.mem_append, List.mem_singleton] at emitted
      rcases emitted with prior | fresh
      · exact Or.inl prior
      · exact Or.inr ⟨material, rfl, fresh⟩

/-- A response advances only the responder's next serial, and only by a fresh
submission. -/
theorem respond_nextSerial (execution : (application setup leaks).Execution) (who : Player)
    (action : (application setup leaks).Action) (observer : Player) :
    (execution.respond (application setup leaks) who action).network.nextSerial observer =
        execution.network.nextSerial observer ∨
      ((∃ material, action.transmission = some material) ∧ observer = who ∧
        (execution.respond (application setup leaks) who action).network.nextSerial observer =
          execution.network.nextSerial who + 1) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl rfl
  | some material =>
      by_cases same : observer = who
      · subst observer
        right
        refine ⟨⟨material, rfl⟩, rfl, ?_⟩
        simp [ReactiveApplication.Execution.respond, MessageNetwork.submit]
      · left
        simp [ReactiveApplication.Execution.respond, MessageNetwork.submit, same]

/-- The token a submission's emission carries names an event whose
prerequisites have completed. -/
theorem packet_token_issued (state : (application setup leaks).State) (who : Player)
    (known : List (Message Player (WitnessedPacket (graph setup))))
    (material : (application setup leaks).Submission) (token : ReadinessToken (graph setup))
    (carried : ((application setup leaks).packet ((application setup leaks).submit state who
      material) who known material).token = some token) :
    ∀ predecessor ∈ (graph setup).order.predecessors token.event,
      predecessor ∈ state.config.cut.completed := by
  rw [reactiveApplication_packet_token] at carried
  unfold PublicView.tokenFor at carried
  obtain ⟨event, _, issued⟩ := Option.bind_eq_some_iff.mp carried
  obtain ⟨rfl, settled⟩ := (state.publicView.readinessToken?_eq_some_iff event token).mp issued
  intro predecessor member
  exact (state.config.history_exact predecessor).mp (settled predecessor member)

theorem settledFacts_respond (execution : (application setup leaks).Execution)
    (facts : SettledFacts setup leaks execution) (who : Player)
    (action : (application setup leaks).Action) :
    SettledFacts setup leaks (execution.respond (application setup leaks) who action) := by
  let app := application setup leaks
  have configEq := ((runtime setup).reactive_respond_application leaks execution who action).1
  have receiptsEq := app.respond_receipts execution who action
  have ledgerEq := app.respond_ledger execution who action
  have identity := (app.messageIdentityInvariant (fun _ _ => PMF.pure .wait)).respond execution
    who action ⟨facts.serials, facts.unique⟩
  have fresh : ∀ material (token : ReadinessToken (graph setup)),
      (app.packet (app.submit execution.application who material) who
        (execution.network.known who) material).token = some token →
      ∀ predecessor ∈ (graph setup).order.predecessors token.event,
        predecessor ∈ execution.application.config.cut.completed :=
    fun material token carried =>
      packet_token_issued execution.application who _ material token carried
  refine
    { serials := identity.1
      unique := identity.2
      receipts := app.receiptsSound_respond _ execution who action facts.receipts
      carried := ?_
      allocated := ?_
      issued := ?_
      accepted := ?_
      single := ?_
      ordered := ?_ }
  · rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact facts.carried
    | some material =>
        apply (facts.carried.mono fun message emitted =>
          respond_emitted_mono execution who _ emitted).submit
        unfold Emitted
        simp [ReactiveApplication.Execution.respond, MessageNetwork.submit]
  · intro observer serial lower
    rcases respond_nextSerial execution who action observer with same | ⟨⟨material, submitted⟩,
        rfl, advanced⟩
    · rw [same] at lower
      obtain ⟨message, emitted, identified⟩ := facts.allocated observer serial lower
      exact ⟨message, respond_emitted_mono execution who action emitted, identified⟩
    · rw [advanced] at lower
      rcases Nat.lt_succ_iff_lt_or_eq.mp lower with below | equal
      · obtain ⟨message, emitted, identified⟩ := facts.allocated observer serial below
        exact ⟨message, respond_emitted_mono execution observer action emitted, identified⟩
      · subst equal
        refine ⟨⟨(observer, execution.network.nextSerial observer),
          app.packet (app.submit execution.application observer material) observer
            (execution.network.known observer) material⟩, ?_, rfl⟩
        rcases action with ⟨transmission⟩
        cases submitted
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · intro message emitted token carried
    rw [configEq]
    rcases respond_emitted facts who action message emitted with prior | ⟨material, _, rfl⟩
    · exact facts.issued message prior token carried
    · exact fresh material token carried
  · intro id member
    rw [receiptsEq] at member
    rw [ledgerEq, configEq]
    exact facts.accepted id member
  · intro first firstMember second secondMember firstAccepted secondAccepted
    rw [ledgerEq] at firstMember secondMember
    rw [receiptsEq] at firstAccepted secondAccepted
    exact facts.single first firstMember second secondMember firstAccepted secondAccepted
  · intro earlier later earlierEmitted laterEmitted sameSender lower accepted
    rw [receiptsEq] at accepted
    rw [configEq]
    rcases respond_emitted facts who action later laterEmitted with laterPrior |
        ⟨material, _, rfl⟩
    · rcases respond_emitted facts who action earlier earlierEmitted with earlierPrior |
          ⟨material, _, rfl⟩
      · exact facts.ordered earlier later earlierPrior laterPrior sameSender lower accepted
      · have bound := facts.emitted_serial laterPrior
        change who = later.id.1 at sameSender
        rw [← sameSender] at bound
        exact absurd lower (Nat.not_lt.mpr (Nat.le_of_lt bound))
    · have published := facts.receipt_published accepted
      obtain ⟨message, member, identified⟩ := List.mem_map.mp published
      have bound := facts.serials.ledger message member
      rw [identified] at bound
      exact absurd bound (Nat.lt_irrefl _)

/-- An included envelope carries its lookup identifier and lands on the ledger. -/
theorem includePending_found (network : MessageNetwork Player (WitnessedPacket (graph setup)))
    (id : MessageId Player) (message : Message Player (WitnessedPacket (graph setup)))
    (found : network.lookup id = some message) :
    message.id = id ∧ message ∈ network.pending ∧
      (network.includePending id).2.ledger = network.ledger ++ [message] := by
  refine ⟨?_, List.mem_of_find?_eq_some found, ?_⟩
  · have identified := (List.find?_eq_some_iff_append.mp found).1
    simpa only [decide_eq_true_eq] using identified
  · simp only [MessageNetwork.includePending, found]

/-- What an accepting inclusion establishes: the envelope's token is valid, its
event was ready and has completed, and its sender is the event's actor. -/
theorem accepted_inclusion (state next : (application setup leaks).State)
    (message : Message Player (WitnessedPacket (graph setup)))
    (handled : (application setup leaks).handle state message = some next) :
    message.payload.tokenValid = true ∧
      ∃ event, message.payload.call.event? (graph setup) = some event ∧
        state.config.cut.Ready event ∧ event ∈ next.config.cut.completed ∧
        (graph setup).actor? event = some message.sender := by
  obtain ⟨valid, call⟩ := reactiveApplication_handle_eq_some (runtime setup) leaks state next
    message handled
  obtain ⟨event, named, ready, action, member⟩ :=
    handle_config_mem_step (runtime setup) state next _ call
  refine ⟨valid, event, named, ready, ?_, handle_sender_actor (runtime setup) state next _ call
    event named⟩
  rw [state.config.step_cut event ready action next.config member]
  exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)

theorem settledFacts_environment (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    SettledFacts setup leaks next := by
  let app := application setup leaks
  obtain ⟨inputsEq, serialEq, effect⟩ :=
    environmentStep_shape setup leaks execution next command reached
  have step := contractStep_environment (runtime setup) leaks execution next command reached
  have identity := (app.messageIdentityInvariant (fun _ _ => PMF.pure command)).environment
    execution next command ⟨facts.serials, facts.unique⟩ (by simp) reached
  have sound := app.receiptsSound_environmentStep _ execution next command facts.receipts
    (fun _ _ _ => trivial) reached
  have emittedEq : ∀ message, Emitted setup leaks next message ↔
      Emitted setup leaks execution message := by
    intro message
    unfold Emitted
    rw [inputsEq]
  have completedMono : ∀ event, event ∈ execution.application.config.cut.completed →
      event ∈ next.application.config.cut.completed :=
    fun _ completed => step.completed_mono completed
  refine
    { serials := identity.1
      unique := identity.2
      receipts := sound
      carried := ?_
      allocated := ?_
      issued := ?_
      accepted := ?_
      single := ?_
      ordered := ?_ }
  · rcases effect with ⟨_, _, keep⟩ | ⟨id, message, found, networkEq, _, _⟩
    · exact keep _ (facts.carried.mono fun message emitted => (emittedEq message).mpr emitted)
    · rw [networkEq]
      exact (facts.carried.mono fun message emitted =>
        (emittedEq message).mpr emitted).includePending id
  · intro who serial lower
    rw [serialEq] at lower
    obtain ⟨message, emitted, identified⟩ := facts.allocated who serial lower
    exact ⟨message, (emittedEq message).mpr emitted, identified⟩
  · intro message emitted token carried predecessor member
    exact completedMono _ (facts.issued message ((emittedEq message).mp emitted) token carried
      predecessor member)
  · rcases effect with ⟨receiptsEq, ledgerEq, _⟩ |
        ⟨id, message, found, networkEq, receiptsEq, applicationEq⟩
    · intro id' member
      rw [receiptsEq] at member
      obtain ⟨accepted, onLedger, identified, valid, event, named, completed, owned⟩ :=
        facts.accepted id' member
      rw [ledgerEq]
      exact ⟨accepted, onLedger, identified, valid, event, named, completedMono event completed,
        owned⟩
    · obtain ⟨addressed, _, ledgerEq⟩ := includePending_found execution.network id message found
      intro id' member
      rw [receiptsEq] at member
      rw [networkEq, ledgerEq]
      rcases List.mem_append.mp member with prior | fresh
      · obtain ⟨accepted, onLedger, identified, valid, event, named, completed, owned⟩ :=
          facts.accepted id' prior
        exact ⟨accepted, List.mem_append_left _ onLedger, identified, valid, event, named,
          completedMono event completed, owned⟩
      · obtain ⟨idEq, isSome⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
        subst idEq
        obtain ⟨after, handled⟩ := Option.isSome_iff_exists.mp isSome.symm
        obtain ⟨valid, event, named, _, completed, owned⟩ :=
          accepted_inclusion execution.application after message handled
        refine ⟨message, List.mem_append_right _ (List.mem_singleton.mpr rfl), addressed, valid,
          event, named, ?_, owned⟩
        rw [applicationEq, handled]
        exact completed
  · rcases effect with ⟨receiptsEq, ledgerEq, _⟩ |
        ⟨id, message, found, networkEq, receiptsEq, applicationEq⟩
    · rw [receiptsEq, ledgerEq]
      exact facts.single
    · obtain ⟨addressed, pending, ledgerEq⟩ :=
        includePending_found execution.network id message found
      -- Every accepted ledger envelope is an old accepted one or the newly accepted one.
      have classify : ∀ candidate ∈ next.network.ledger,
          (candidate.id, true) ∈ next.receipts →
          (candidate ∈ execution.network.ledger ∧
              (candidate.id, true) ∈ execution.receipts) ∨
            (candidate = message ∧
              (app.handle execution.application message).isSome = true) := by
        intro candidate onLedger accepted
        rw [networkEq, ledgerEq] at onLedger
        rw [receiptsEq] at accepted
        rcases List.mem_append.mp accepted with prior | fresh
        · left
          refine ⟨?_, prior⟩
          rcases List.mem_append.mp onLedger with old | new
          · exact old
          · cases List.mem_singleton.mp new
            obtain ⟨other, otherMember, identified, _⟩ := facts.accepted _ prior
            have same := (facts.unique.ledger other otherMember).pending message pending
              identified.symm
            rw [same]
            exact otherMember
        · obtain ⟨idEq, isSome⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
          right
          refine ⟨?_, isSome.symm⟩
          rcases List.mem_append.mp onLedger with old | new
          · exact (facts.unique.pending message pending).ledger candidate old
              (idEq.trans addressed.symm)
          · exact List.mem_singleton.mp new
      intro first firstMember second secondMember firstAccepted secondAccepted event
        firstNamed secondNamed
      have readyFresh : ∀ (other : Message Player (WitnessedPacket (graph setup))),
          other ∈ execution.network.ledger → (other.id, true) ∈ execution.receipts →
          other.payload.call.event? (graph setup) = some event →
          (app.handle execution.application message).isSome = true →
          message.payload.call.event? (graph setup) = some event → False := by
        intro other otherMember otherAccepted otherNamed isSome messageNamed
        obtain ⟨after, handled⟩ := Option.isSome_iff_exists.mp isSome
        obtain ⟨_, readyEvent, named, ready, _, _⟩ :=
          accepted_inclusion execution.application after message handled
        rw [messageNamed] at named
        cases Option.some.inj named
        obtain ⟨witness, witnessMember, identified, _, completedEvent, completedNamed,
          completed, _⟩ := facts.accepted other.id otherAccepted
        have same := (facts.unique.ledger witness witnessMember).ledger other otherMember
          identified.symm
        rw [← same, otherNamed] at completedNamed
        cases Option.some.inj completedNamed
        exact ready.1 completed
      rcases classify first firstMember firstAccepted with ⟨firstOld, firstPrior⟩ |
          ⟨firstNew, firstSome⟩ <;>
        rcases classify second secondMember secondAccepted with ⟨secondOld, secondPrior⟩ |
          ⟨secondNew, secondSome⟩
      · exact facts.single first firstOld second secondOld firstPrior secondPrior event
          firstNamed secondNamed
      · subst secondNew
        exact (readyFresh first firstOld firstPrior firstNamed secondSome secondNamed).elim
      · subst firstNew
        exact (readyFresh second secondOld secondPrior secondNamed firstSome firstNamed).elim
      · rw [firstNew, secondNew]
  · intro earlier later earlierEmitted laterEmitted sameSender lower accepted valid event
      named
    rcases effect with ⟨receiptsEq, _, _⟩ |
        ⟨id, message, found, networkEq, receiptsEq, applicationEq⟩
    · rw [receiptsEq] at accepted
      exact completedMono event (facts.ordered earlier later ((emittedEq earlier).mp
        earlierEmitted) ((emittedEq later).mp laterEmitted) sameSender lower accepted valid
          event named)
    · rw [receiptsEq] at accepted
      rcases List.mem_append.mp accepted with prior | fresh
      · exact completedMono event (facts.ordered earlier later ((emittedEq earlier).mp
          earlierEmitted) ((emittedEq later).mp laterEmitted) sameSender lower prior valid
            event named)
      · obtain ⟨_, isSome⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
        obtain ⟨after, handled⟩ := Option.isSome_iff_exists.mp isSome.symm
        obtain ⟨_, accepted', _, ready, completed, _⟩ :=
          accepted_inclusion execution.application after message handled
        obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ :=
          (WitnessedPacket.tokenValid_iff earlier.payload).mp valid
        rw [named] at tokenNamed
        cases Option.some.inj tokenNamed
        have settled := facts.issued earlier ((emittedEq earlier).mp earlierEmitted) ⟨event⟩
          tokenEq
        by_cases done : event ∈ execution.application.config.cut.completed
        · exact completedMono event done
        · have readyEarlier : execution.application.config.cut.Ready event :=
            ⟨done, fun predecessor member => settled predecessor member⟩
          cases ready_unique execution.application.config.cut readyEarlier ready
          rw [applicationEq, handled]
          exact completed

theorem settledFacts_serviceInvariant (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler (SettledFacts setup leaks) where
  respond execution who action facts := settledFacts_respond execution facts who action
  environment execution next command facts _ reached :=
    settledFacts_environment execution next command facts reached

/-- The settled facts hold at every legal history, for every scheduler and
arbitrary responses. -/
theorem settledFacts_history (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    SettledFacts setup leaks control.execution :=
  (settledFacts_serviceInvariant scheduler).history initial horizon
    (fun state _ => settledFacts_initial state) trace

end Facts

section Marks

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The packet's content alone rules it out at every settlement. -/
def ContentForbidden (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  message.payload.tokenValid = false ∨
    SignedContentBreach message ∨
    (∃ event, message.payload.call.event? (graph setup) = some event ∧
      (graph setup).actor? event ≠ some message.sender)

/-- The handler's public conditions on a call, other than readiness and the
sender's authority. -/
def PublicConditions (state : EventGraphRuntime.State (graph setup))
    (call : Payload (graph setup)) : Prop :=
  match call with
  | .commitment event candidate =>
      state.WithinDeadline (runtime setup) event ∧
        match nodeView (graph setup) event with
        | .bind owner _ _ _ => candidate.1 = owner ∧ state.accepted (.inr event) = none ∧
            state.HandleUnused candidate
        | .resolve .. | .sample .. => False
  | .opening event candidate raw =>
      state.WithinDeadline (runtime setup) event ∧
        match nodeView (graph setup) event with
        | .resolve owner payload binding _ _ _ => candidate.1 = owner ∧
            state.accepted binding.field = some candidate ∧ raw.ty = payload
        | .bind .. | .sample .. => False
  | .withhold event =>
      state.WithinDeadline (runtime setup) event ∧
        match nodeView (graph setup) event with
        | .resolve .. => True
        | .bind .. | .sample .. => False
  | .malformed _ => True

/-- Accepting the packet at this state would settle content the record
rejects: a commitment to another handle than the author's next prepared one, or
an opening whose guards reject the value. -/
def ContentFails (state : EventGraphRuntime.State (graph setup))
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  match message.payload.call with
  | .commitment _ candidate =>
      candidate ≠ (message.sender, .prepared (state.publicView.bindingCount message.sender))
  | .opening _ _ _ => state.publicView.openingGuardsAccepted message.payload = false
  | .withhold _ | .malformed _ => False

/-- A packet the settled record forbids at every complete settlement after
this execution: its content is ruled out; or it is not accepted, and either its
event has completed, or its event is ready and the handler cannot accept it
before the event completes, or the record will reject its content if it does;
or it is accepted with content the record rejects. -/
def Condemned (execution : (application setup leaks).Execution)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  ContentForbidden setup message ∨
    (∃ event, message.payload.call.event? (graph setup) = some event ∧
      (message.id, true) ∉ execution.receipts ∧
      (event ∈ execution.application.config.cut.completed ∨
        (execution.application.config.cut.Ready event ∧
          (¬ PublicConditions setup execution.application message.payload.call ∨
            ContentFails setup execution.application message)))) ∨
    ((message.id, true) ∈ execution.receipts ∧
      ∃ event, message.payload.call.event? (graph setup) = some event ∧
        event ∈ execution.application.config.cut.completed ∧
        ¬ ((runtime setup).settledRecord leaks execution).SettledContent message)

/-- Some packet of `who` is forbidden at every complete settlement after this
execution: one is condemned, or two of its identifiers address one event. -/
def Doomed (execution : (application setup leaks).Execution) (who : Player) : Prop :=
  ∃ message, Emitted setup leaks execution message ∧ message.sender = who ∧
    (Condemned setup leaks execution message ∨
      ∃ other, Emitted setup leaks execution other ∧ other.sender = who ∧
        other.id ≠ message.id ∧ ∃ event, message.payload.call.event? (graph setup) = some event ∧
          other.payload.call.event? (graph setup) = some event)

variable {setup leaks}

/-- An accepting inclusion met the handler's public conditions. -/
theorem handle_publicConditions (state next : EventGraphRuntime.State (graph setup))
    (id : MessageId Player) (call : Payload (graph setup))
    (accepted : handle (runtime setup) state ⟨id, call⟩ = some next) :
    PublicConditions setup state call := by
  classical
  cases call with
  | malformed raw => trivial
  | withhold event =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline (runtime setup) event
        · refine ⟨timely, ?_⟩
          cases node : nodeView (graph setup) event with
          | resolve owner payload binding checks outputEq codeEq => trivial
          | bind owner payload outputEq codeEq =>
              simp [handle, ready, timely, node] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, node] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | commitment event candidate =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline (runtime setup) event
        · refine ⟨timely, ?_⟩
          cases view : nodeView (graph setup) event with
          | bind owner payload outputEq codeEq =>
              by_cases handleOwner : candidate.1 = owner
              · by_cases vacant : state.accepted (.inr event) = none
                · by_cases unused : state.HandleUnused candidate
                  · exact ⟨handleOwner, vacant, unused⟩
                  · simp [handle, ready, timely, view, handleOwner, vacant, unused] at accepted
                · simp [handle, ready, timely, view, handleOwner, vacant] at accepted
              · simp [handle, ready, timely, view, handleOwner] at accepted
          | resolve owner payload binding checks outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | opening event candidate raw =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline (runtime setup) event
        · refine ⟨timely, ?_⟩
          cases view : nodeView (graph setup) event with
          | resolve owner payload binding checks outputEq codeEq =>
              by_cases handleOwner : candidate.1 = owner
              · by_cases associated : state.accepted binding.field = some candidate
                · by_cases typed : raw.ty = payload
                  · exact ⟨handleOwner, associated, typed⟩
                  · have untyped : raw.as? payload = none := by simp [Raw.as?, typed]
                    by_cases verified : state.candidates.verify candidate raw = true
                    · simp only [handle, ready, ↓reduceDIte, timely, view, handleOwner, associated,
                        verified, dite_eq_ite, Option.ite_none_right_eq_some] at accepted
                      obtain ⟨_, matched⟩ := accepted
                      split at matched
                      · cases matched
                      · rename_i value typedEq
                        rw [untyped] at typedEq
                        cases typedEq
                    · simp [handle, ready, timely, view, handleOwner, associated, verified]
                        at accepted
                · simp [handle, ready, timely, view, handleOwner, associated] at accepted
              · simp [handle, ready, timely, view, handleOwner] at accepted
          | bind owner payload outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted

/-- A packet whose content is allowed, whose event is ready, and which meets the
handler's public conditions with content the record accepts, conforms on the
current public view. -/
theorem fresh_of_conditions (state : EventGraphRuntime.State (graph setup))
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (named : message.payload.call.event? (graph setup) = some event)
    (allowed : ¬ ContentForbidden setup message) (ready : state.config.cut.Ready event)
    (conditions : PublicConditions setup state message.payload.call)
    (content : ¬ ContentFails setup state message) :
    (runtime setup).freshServiceEnvelope state.publicView message := by
  have valid : message.payload.tokenValid = true := by
    by_contra invalid
    exact allowed (Or.inl (Bool.eq_false_iff.mpr invalid))
  have owned : (graph setup).actor? event = some message.sender := by
    by_contra foreign
    exact allowed (Or.inr (Or.inr ⟨event, named, foreign⟩))
  obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ :=
    (WitnessedPacket.tokenValid_iff message.payload).mp valid
  rw [named] at tokenNamed
  cases Option.some.inj tokenNamed
  have readyView := (state.publicView_eventReady event).mpr ready
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  change token = some ⟨event⟩ at tokenEq
  subst tokenEq
  cases call with
  | malformed raw => cases named
  | withhold actual =>
      change some actual = some event at named
      cases Option.some.inj named
      have empty : evidence = none := by
        by_contra present
        exact allowed (Or.inr (Or.inl (Or.inr (Or.inl ⟨event, rfl, present⟩))))
      obtain ⟨timely, resolving⟩ := conditions
      cases node : nodeView (graph setup) event with
      | resolve owner payload binding checks outputEq codeEq =>
          have authored : id.1 = owner := by
            have actor := nodeView_resolve_actor outputEq codeEq
            rw [owned] at actor
            exact Option.some.inj actor
          exact ((runtime setup).freshServiceEnvelope_withhold_iff state.publicView id event
            owner payload binding checks outputEq codeEq node evidence (some ⟨event⟩)).mpr
              ⟨readyView, timely, empty, rfl, authored⟩
      | bind owner payload outputEq codeEq => simp only [node] at resolving
      | sample payload law outputEq codeEq => simp only [node] at resolving
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      have empty : evidence = none := by
        by_contra present
        exact allowed (Or.inr (Or.inl
          (Or.inr (Or.inr (Or.inl ⟨event, candidate, rfl, present⟩)))))
      have canonical : candidate = (id.1, .prepared (state.publicView.bindingCount id.1)) := by
        by_contra other
        exact content other
      refine ((runtime setup).freshServiceEnvelope_binding_iff state.publicView id event
        candidate evidence (some ⟨event⟩)).mpr ⟨?_, canonical, empty, rfl⟩
      obtain ⟨timely, rest⟩ := conditions
      refine ⟨readyView, timely, ?_⟩
      cases view : nodeView (graph setup) event with
      | bind owner payload outputEq codeEq =>
          simp only [view] at rest
          obtain ⟨handleOwner, vacant, unused⟩ := rest
          have authored : id.1 = owner := by
            have actor := nodeView_bind_actor outputEq codeEq
            rw [owned] at actor
            exact Option.some.inj actor
          exact ⟨authored, handleOwner, vacant, unused⟩
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [view] at rest
      | sample payload law outputEq codeEq =>
          simp only [view] at rest
  | opening actual candidate raw =>
      change some actual = some event at named
      cases Option.some.inj named
      have certified : certifiedOpening
          (⟨.opening event candidate raw, evidence, some ⟨event⟩⟩ :
            WitnessedPacket (graph setup)) = true := by
        by_contra uncertified
        exact allowed (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨event, candidate, raw, rfl,
          Bool.eq_false_iff.mpr uncertified⟩)))))
      have guarded : state.publicView.openingGuardsAccepted
          ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩ = true := by
        by_contra rejected
        exact content (Bool.eq_false_iff.mpr rejected)
      obtain ⟨timely, rest⟩ := conditions
      cases view : nodeView (graph setup) event with
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [view] at rest
          obtain ⟨handleOwner, associated, typed⟩ := rest
          have authored : id.1 = owner := by
            have actor := nodeView_resolve_actor outputEq codeEq
            rw [owned] at actor
            exact Option.some.inj actor
          exact ((runtime setup).freshServiceEnvelope_opening_iff state.publicView id event
            owner payload binding checks outputEq codeEq view candidate raw evidence
            (some ⟨event⟩)).mpr ⟨readyView, timely, certified, guarded, authored, handleOwner,
              associated, typed, rfl⟩
      | bind owner payload outputEq codeEq =>
          simp only [view] at rest
      | sample payload law outputEq codeEq =>
          simp only [view] at rest

omit [IExpr.ResultTypes L] in
/-- A ledger holding the first `count` identifiers of an author counts at least
`count` of them. -/
theorem distinctAuthoredCount_ge {Payload : Type} (ledger : List (Message Player Payload))
    (who : Player) (count : Nat)
    (present : ∀ serial < count, (who, serial) ∈ ledger.map Message.id) :
    count ≤ Message.distinctAuthoredCount ledger who := by
  unfold Message.distinctAuthoredCount
  have subset : (Finset.range count).image (fun serial => (who, serial)) ⊆
      (ledger.map Message.id).toFinset.filter fun id => id.1 = who := by
    intro id member
    obtain ⟨serial, inside, rfl⟩ := Finset.mem_image.mp member
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (present serial
      (Finset.mem_range.mp inside)), rfl⟩
  calc
    count = ((Finset.range count).image (fun serial => (who, serial))).card := by
      rw [Finset.card_image_of_injective _ (fun first second same => by
        simpa using same), Finset.card_range]
    _ ≤ _ := Finset.card_le_card subset

omit [IExpr.ResultTypes L] in
/-- A ledger holding only identifiers of an author below `count` counts at most
`count` of them. -/
theorem distinctAuthoredCount_le {Payload : Type} (ledger : List (Message Player Payload))
    (who : Player) (count : Nat)
    (below : ∀ id ∈ ledger.map Message.id, id.1 = who → id.2 < count) :
    Message.distinctAuthoredCount ledger who ≤ count := by
  unfold Message.distinctAuthoredCount
  have subset : ((ledger.map Message.id).toFinset.filter fun id => id.1 = who) ⊆
      (Finset.range count).image (fun serial => (who, serial)) := by
    intro id member
    obtain ⟨inside, owned⟩ := Finset.mem_filter.mp member
    refine Finset.mem_image.mpr ⟨id.2, Finset.mem_range.mpr
      (below id (List.mem_toFinset.mp inside) owned), ?_⟩
    rw [← owned]
  calc
    _ ≤ ((Finset.range count).image (fun serial => (who, serial))).card :=
      Finset.card_le_card subset
    _ ≤ (Finset.range count).card := Finset.card_image_le
    _ = count := Finset.card_range count

/-- **A breach at transmission dooms its author.** A packet emitted by a response
that breaks the send-time conformance rule on the public view and ledger the
response saw leaves its author with a packet forbidden at every complete
settlement. -/
theorem doomed_of_breach (execution : (application setup leaks).Execution)
    (facts : SettledFacts setup leaks execution) (who : Player)
    (action : (application setup leaks).Action)
    (message : Message Player (WitnessedPacket (graph setup)))
    (emitted : Emitted setup leaks (execution.respond (application setup leaks) who action)
      message)
    (breach : (runtime setup).permittedServiceEnvelope execution.application.publicView
      execution.network.ledger message = false) :
    Doomed setup leaks (execution.respond (application setup leaks) who action)
      message.sender := by
  classical
  have after := settledFacts_respond execution facts who action
  have publicEq : (execution.respond (application setup leaks) who action).application.publicView =
      execution.application.publicView :=
    ((runtime setup).reactive_respond_application leaks execution who action).2
  have ledgerEq : (execution.respond (application setup leaks) who action).network.ledger =
      execution.network.ledger := (application setup leaks).respond_ledger execution who action
  generalize execution.respond (application setup leaks) who action = next at *
  have unpublished : message.id ∉ next.network.ledger.map Message.id := by
    intro published
    rw [ledgerEq] at published
    rw [(runtime setup).permittedServiceEnvelope_published _ _ _ published] at breach
    cases breach
  have unaccepted : (message.id, true) ∉ next.receipts :=
    fun accepted => unpublished (after.receipt_published accepted)
  by_cases forbidden : ContentForbidden setup message
  · exact ⟨message, emitted, rfl, Or.inl (Or.inl forbidden)⟩
  -- A different identifier of the author, not accepted, dooms the author.
  have doomedBy : ∀ other, Emitted setup leaks next other → other.sender = message.sender →
      other.id ≠ message.id → (other.id, true) ∉ next.receipts →
      ∀ event, message.payload.call.event? (graph setup) = some event →
      next.application.config.cut.Ready event → Doomed setup leaks next message.sender := by
    intro other otherEmitted otherSender different otherUnaccepted event named ready
    by_cases otherForbidden : ContentForbidden setup other
    · exact ⟨other, otherEmitted, otherSender, Or.inl (Or.inl otherForbidden)⟩
    have otherValid : other.payload.tokenValid = true := by
      by_contra invalid
      exact otherForbidden (Or.inl (Bool.eq_false_iff.mpr invalid))
    obtain ⟨otherEvent, otherNamed, otherToken⟩ :=
      (WitnessedPacket.tokenValid_iff other.payload).mp otherValid
    have otherSettled := after.issued other otherEmitted ⟨otherEvent⟩ otherToken
    by_cases otherDone : otherEvent ∈ next.application.config.cut.completed
    · exact ⟨other, otherEmitted, otherSender, Or.inl (Or.inr (Or.inl ⟨otherEvent, otherNamed,
        otherUnaccepted, Or.inl otherDone⟩))⟩
    · have otherReady : next.application.config.cut.Ready otherEvent :=
        ⟨otherDone, fun predecessor member => otherSettled predecessor member⟩
      cases ready_unique next.application.config.cut otherReady ready
      exact ⟨message, emitted, rfl, Or.inr ⟨other, otherEmitted, otherSender, different,
        _, named, otherNamed⟩⟩
  have valid : message.payload.tokenValid = true := by
    by_contra invalid
    exact forbidden (Or.inl (Bool.eq_false_iff.mpr invalid))
  obtain ⟨event, named, tokenEq⟩ := (WitnessedPacket.tokenValid_iff message.payload).mp valid
  have settled := after.issued message emitted ⟨event⟩ tokenEq
  by_cases done : event ∈ next.application.config.cut.completed
  · exact ⟨message, emitted, rfl, Or.inl (Or.inr (Or.inl ⟨event, named, unaccepted,
      Or.inl done⟩))⟩
  have ready : next.application.config.cut.Ready event :=
    ⟨done, fun predecessor member => settled predecessor member⟩
  by_cases conditions : PublicConditions setup next.application message.payload.call
  swap
  · exact ⟨message, emitted, rfl, Or.inl (Or.inr (Or.inl ⟨event, named, unaccepted,
      Or.inr ⟨ready, Or.inl conditions⟩⟩))⟩
  by_cases fails : ContentFails setup next.application message
  · exact ⟨message, emitted, rfl, Or.inl (Or.inr (Or.inl ⟨event, named, unaccepted,
      Or.inr ⟨ready, Or.inr fails⟩⟩))⟩
  have fresh := fresh_of_conditions next.application message event named forbidden ready
    conditions fails
  rw [publicEq] at fresh
  have wrongSerial : message.id.2 ≠
      Message.distinctAuthoredCount next.network.ledger message.sender := by
    intro serial
    rw [ledgerEq] at serial
    rw [((runtime setup).permittedServiceEnvelope_iff _ _ _).mpr (Or.inr ⟨serial, fresh⟩)]
      at breach
    cases breach
  rcases Nat.lt_or_gt_of_ne wrongSerial with below | above
  · -- A later identifier of the author is already on the ledger.
    obtain ⟨id, member, owned, later⟩ : ∃ id ∈ next.network.ledger.map Message.id,
        id.1 = message.sender ∧ message.id.2 < id.2 := by
      by_contra absent
      simp only [not_exists, not_and, not_lt] at absent
      have bound := distinctAuthoredCount_le next.network.ledger message.sender message.id.2
        (fun id member owned => by
          have notAfter := absent id member owned
          rcases Nat.lt_or_ge id.2 message.id.2 with lower | upper
          · exact lower
          · have same : id = message.id :=
              Prod.ext (owned.trans rfl) (le_antisymm notAfter upper)
            exact absurd (same ▸ member) unpublished)
      exact absurd below (Nat.not_lt.mpr bound)
    obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
    have otherEmitted := after.carried.ledger other otherMember
    by_cases accepted : (other.id, true) ∈ next.receipts
    · exact (done (after.ordered message other emitted otherEmitted owned.symm later accepted
        valid event named)).elim
    · exact doomedBy other otherEmitted owned (fun same => by
        rw [same] at later
        exact Nat.lt_irrefl _ later) accepted event named ready
  · -- An earlier identifier of the author is not on the ledger.
    obtain ⟨serial, lower, absent⟩ : ∃ serial < message.id.2,
        (message.sender, serial) ∉ next.network.ledger.map Message.id := by
      by_contra present
      simp only [not_exists, not_and, not_not] at present
      exact absurd above (Nat.not_lt.mpr
        (distinctAuthoredCount_ge next.network.ledger message.sender message.id.2 present))
    obtain ⟨other, otherEmitted, identified⟩ := after.allocated message.sender serial
      (lower.trans (after.emitted_serial emitted))
    have otherSender : other.sender = message.sender := by
      change other.id.1 = message.id.1
      rw [identified]
      rfl
    refine doomedBy other otherEmitted otherSender (fun same => ?_) (fun accepted => ?_) event
      named ready
    · have serialEq := congrArg Prod.snd (identified.symm.trans same)
      exact Nat.lt_irrefl _ (serialEq ▸ lower)
    · exact absent (identified ▸ after.receipt_published accepted)

/-- The handler's public conditions only weaken as the clock advances. -/
theorem publicConditions_of_later (first second : EventGraphRuntime.State (graph setup))
    (acceptedEq : second.accepted = first.accepted)
    (activatedEq : second.activatedAt = first.activatedAt)
    (clockLe : first.clock ≤ second.clock) (call : Payload (graph setup))
    (holds : PublicConditions setup second call) : PublicConditions setup first call := by
  have timely : ∀ event, second.WithinDeadline (runtime setup) event →
      first.WithinDeadline (runtime setup) event := by
    intro event within
    unfold State.WithinDeadline at within ⊢
    rw [activatedEq] at within
    cases activated : first.activatedAt event with
    | none =>
        rw [activated] at within
        exact within
    | some entered =>
        rw [activated] at within
        exact lt_of_le_of_lt (Nat.sub_le_sub_right clockLe entered) within
  cases call with
  | malformed raw => trivial
  | withhold event =>
      exact ⟨timely event holds.1, holds.2⟩
  | commitment event candidate =>
      obtain ⟨within, rest⟩ := holds
      refine ⟨timely event within, ?_⟩
      cases view : nodeView (graph setup) event with
      | bind owner payload outputEq codeEq =>
          simp only [view] at rest ⊢
          obtain ⟨handleOwner, vacant, unused⟩ := rest
          refine ⟨handleOwner, acceptedEq ▸ vacant, fun field => ?_⟩
          have other := unused field
          rw [acceptedEq] at other
          exact other
      | resolve _ _ _ _ _ _ => simp only [view] at rest
      | sample _ _ _ _ => simp only [view] at rest
  | opening event candidate raw =>
      obtain ⟨within, rest⟩ := holds
      refine ⟨timely event within, ?_⟩
      cases view : nodeView (graph setup) event with
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [view] at rest ⊢
          obtain ⟨handleOwner, associated, typed⟩ := rest
          exact ⟨handleOwner, acceptedEq ▸ associated, typed⟩
      | bind _ _ _ _ => simp only [view] at rest
      | sample _ _ _ _ => simp only [view] at rest

/-- The settled content of a packet for a completed event is fixed by every
later contract step. -/
theorem settledContent_of_step {before after : EventGraphRuntime.State (graph setup)}
    (step : ContractStep before after)
    (beforeReceipts afterReceipts : List (MessageId Player × Bool))
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (named : message.payload.call.event? (graph setup) = some event)
    (completed : event ∈ before.config.cut.completed)
    (content : (⟨after.publicView, afterReceipts⟩ : SettledRecord (graph setup)).SettledContent
      message) :
    (⟨before.publicView, beforeReceipts⟩ : SettledRecord (graph setup)).SettledContent message := by
  obtain ⟨rest, extended⟩ := step.order_extends
  have member : event ∈ before.publicView.observation.completionOrder :=
    (before.config.history_exact event).mpr completed
  have guardsEq := State.openingGuardsAccepted_congr before after message.payload event named
    (fun predecessor inside => before.config.cut.predecessor_closed completed inside)
    (fun field value stored => step.store_retained field value stored)
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | malformed raw => exact content.elim
  | withhold actual => exact content
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      obtain ⟨empty, canonical⟩ := content
      refine ⟨empty, ?_⟩
      change candidate = (id.1, .prepared (after.publicView.bindingCountBefore id.1 event))
        at canonical
      change candidate = (id.1, .prepared (before.publicView.bindingCountBefore id.1 event))
      rw [canonical, PublicView.bindingCountBefore_append before.publicView after.publicView id.1
        event member rest extended]
  | opening actual candidate raw =>
      obtain ⟨certified, guarded⟩ := content
      refine ⟨certified, ?_⟩
      change after.publicView.openingGuardsAccepted _ = true at guarded
      change before.publicView.openingGuardsAccepted _ = true
      rw [← guardsEq]
      exact guarded

/-- A packet that becomes accepted at one scheduler step was included by it, and
the contract accepted that very envelope. -/
theorem newly_accepted {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command} (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks execution message)
    (before : (message.id, true) ∉ execution.receipts)
    (after : (message.id, true) ∈ next.receipts) :
    ∃ state, (application setup leaks).handle execution.application message = some state ∧
      next.application = state := by
  obtain ⟨_, _, effect⟩ := environmentStep_shape setup leaks execution next command reached
  rcases effect with ⟨receiptsEq, _, _⟩ | ⟨id, included, found, _, receiptsEq, applicationEq⟩
  · rw [receiptsEq] at after
    exact (before after).elim
  · rw [receiptsEq] at after
    rcases List.mem_append.mp after with prior | fresh
    · exact (before prior).elim
    · obtain ⟨idEq, isSome⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
      obtain ⟨addressed, pending, _⟩ := includePending_found execution.network id included found
      have same : included = message := facts.emitted_unique (facts.carried.pending included
        pending) emitted (addressed.trans idEq.symm)
      subst same
      obtain ⟨state, handled⟩ := Option.isSome_iff_exists.mp isSome.symm
      refine ⟨state, handled, ?_⟩
      rw [applicationEq, handled]
      rfl

/-- A condemned packet stays condemned across a response: it changes no
completion, receipt or public contract state. -/
theorem Condemned.respond {execution : (application setup leaks).Execution}
    {message : Message Player (WitnessedPacket (graph setup))}
    (marked : Condemned setup leaks execution message) (who : Player)
    (action : (application setup leaks).Action) :
    Condemned setup leaks (execution.respond (application setup leaks) who action) message := by
  obtain ⟨configEq, publicEq⟩ := (runtime setup).reactive_respond_application leaks execution
    who action
  have receiptsEq := (application setup leaks).respond_receipts execution who action
  have acceptedEq := congrArg PublicView.accepted publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  have clockEq := congrArg PublicView.clock publicEq
  rcases marked with forbidden | ⟨event, named, unaccepted, state⟩ |
      ⟨accepted, event, named, completed, content⟩
  · exact Or.inl forbidden
  · refine Or.inr (Or.inl ⟨event, named, receiptsEq ▸ unaccepted, ?_⟩)
    rw [configEq]
    rcases state with done | ⟨ready, blocked | fails⟩
    · exact Or.inl done
    · refine Or.inr ⟨ready, Or.inl fun holds => blocked ?_⟩
      exact publicConditions_of_later _ _ acceptedEq activatedEq (le_of_eq clockEq.symm) _
        holds
    · refine Or.inr ⟨ready, Or.inr ?_⟩
      unfold ContentFails at fails ⊢
      rw [publicEq]
      exact fails
  · refine Or.inr (Or.inr ⟨receiptsEq ▸ accepted, event, named, configEq ▸ completed, ?_⟩)
    unfold settledRecord at content ⊢
    rw [publicEq, receiptsEq]
    exact content

/-- Marks survive a response: it changes no completion, receipt or public
contract state. -/
theorem Doomed.respond {execution : (application setup leaks).Execution} {owner : Player}
    (doomed : Doomed setup leaks execution owner) (who : Player)
    (action : (application setup leaks).Action) :
    Doomed setup leaks (execution.respond (application setup leaks) who action) owner := by
  obtain ⟨message, emitted, authored, marked | ⟨other, otherEmitted, otherAuthored, different,
    event, named, otherNamed⟩⟩ := doomed
  · exact ⟨message, respond_emitted_mono execution who action emitted, authored,
      Or.inl (marked.respond who action)⟩
  · exact ⟨message, respond_emitted_mono execution who action emitted, authored,
      Or.inr ⟨other, respond_emitted_mono execution who action otherEmitted, otherAuthored,
        different, event, named, otherNamed⟩⟩

/-- A condemned emitted packet stays condemned across a scheduler command. -/
theorem Condemned.environment {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command} (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks execution message)
    (marked : Condemned setup leaks execution message) :
    Condemned setup leaks next message := by
  obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
  have step := contractStep_environment (runtime setup) leaks execution next command reached
  have prefixOf := (application setup leaks).environmentStep_receipts_prefix execution next
    command reached
  have emittedEq : ∀ message, Emitted setup leaks execution message →
      Emitted setup leaks next message := by
    intro message emitted
    unfold Emitted at emitted ⊢
    rw [inputsEq]
    exact emitted
  rcases marked with forbidden | ⟨event, named, unaccepted, state⟩ |
      ⟨accepted, event, named, completed, content⟩
  · exact Or.inl forbidden
  · by_cases acceptedNow : (message.id, true) ∈ next.receipts
    · obtain ⟨after, handled, applicationEq⟩ :=
        newly_accepted facts reached emitted unaccepted acceptedNow
      obtain ⟨_, acceptedEvent, acceptedNamed, acceptedReady, acceptedCompleted, _⟩ :=
        accepted_inclusion execution.application after message handled
      rw [named] at acceptedNamed
      cases Option.some.inj acceptedNamed
      rcases state with done | ⟨ready, blocked | fails⟩
      · exact (acceptedReady.1 done).elim
      · exact (blocked (handle_publicConditions execution.application after message.id
          message.payload.call (reactiveHandle_call handled))).elim
      · refine Or.inr (Or.inr ⟨acceptedNow, event, named, applicationEq ▸ acceptedCompleted,
          fun content => ?_⟩)
        obtain ⟨stepEvent, stepNamed, _, action, member⟩ := handle_config_mem_step
          (runtime setup) execution.application after _ (reactiveHandle_call handled)
        have sameEvent : stepEvent = event := Option.some.inj (stepNamed.symm.trans named)
        subst stepEvent
        have orderEq : after.publicView.observation.completionOrder =
            execution.application.publicView.observation.completionOrder ++ [event] := by
          change after.config.history.map Completion.event =
            execution.application.config.history.map Completion.event ++ [event]
          rw [execution.application.config.step_history event ready action after.config
            member]
          simp
        have absent : event ∉ execution.application.publicView.observation.completionOrder :=
          fun inside => ready.1 ((execution.application.config.history_exact event).mp inside)
        have guardsEq := State.openingGuardsAccepted_congr execution.application after
          message.payload event named (fun predecessor inside => ready.2 inside)
          (fun field value stored => execution.application.config.step_store_of_some
            after.config event ready action member field value stored)
        unfold settledRecord at content
        rw [applicationEq] at content
        rcases message with ⟨id, ⟨call, evidence, token⟩⟩
        cases call with
        | malformed raw => exact content.elim
        | withhold actual => exact fails.elim
        | commitment actual candidate =>
            change some actual = some event at named
            cases Option.some.inj named
            obtain ⟨_, canonical⟩ := content
            change candidate = (id.1, .prepared (after.publicView.bindingCountBefore id.1
              event)) at canonical
            change candidate ≠ (id.1, .prepared (execution.application.publicView.bindingCount
              id.1)) at fails
            rw [PublicView.bindingCountBefore_complete execution.application.publicView
              after.publicView id.1 event absent [] orderEq] at canonical
            exact fails canonical
        | opening actual candidate raw =>
            obtain ⟨_, guarded⟩ := content
            change after.publicView.openingGuardsAccepted _ = true at guarded
            change execution.application.publicView.openingGuardsAccepted _ = false at fails
            rw [← guardsEq, guarded] at fails
            cases fails
    · refine Or.inr (Or.inl ⟨event, named, acceptedNow, ?_⟩)
      rcases state with done | ⟨ready, blocked | fails⟩
      · exact Or.inl (step.completed_mono done)
      · rcases step with ⟨configEq, acceptedEq, activatedEq, clockLe⟩ |
          ⟨other, otherReady, action, member⟩
        · refine Or.inr ⟨configEq ▸ ready, Or.inl fun holds => blocked ?_⟩
          exact publicConditions_of_later _ _ acceptedEq activatedEq clockLe _ holds
        · cases ready_unique _ otherReady ready
          refine Or.inl ?_
          rw [execution.application.config.step_cut event otherReady action
            next.application.config member]
          exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
      · rcases step with ⟨configEq, _, _, _⟩ | ⟨other, otherReady, action, member⟩
        · refine Or.inr ⟨configEq ▸ ready, Or.inr ?_⟩
          have observationEq : next.application.publicView.observation =
              execution.application.publicView.observation := by
            change (graph setup).publicObserve next.application.config =
              (graph setup).publicObserve execution.application.config
            rw [configEq]
          unfold ContentFails at fails ⊢
          cases call : message.payload.call with
          | commitment actual candidate =>
              simp only [call] at fails ⊢
              rw [PublicView.bindingCount_eq_countP, observationEq,
                ← PublicView.bindingCount_eq_countP]
              exact fails
          | opening actual candidate raw =>
              simp only [call] at fails ⊢
              unfold PublicView.openingGuardsAccepted at fails ⊢
              rw [observationEq]
              exact fails
          | withhold actual => simp only [call] at fails
          | malformed raw => simp only [call] at fails
        · cases ready_unique _ otherReady ready
          refine Or.inl ?_
          rw [execution.application.config.step_cut event otherReady action
            next.application.config member]
          exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
  · refine Or.inr (Or.inr ⟨prefixOf.subset accepted, event, named,
      step.completed_mono completed, fun later => content ?_⟩)
    exact settledContent_of_step step execution.receipts next.receipts message event named
      completed later

/-- Marks survive a scheduler command. -/
theorem Doomed.environment {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command} (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {owner : Player} (doomed : Doomed setup leaks execution owner) :
    Doomed setup leaks next owner := by
  obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
  have step := contractStep_environment (runtime setup) leaks execution next command reached
  have prefixOf := (application setup leaks).environmentStep_receipts_prefix execution next
    command reached
  have emittedEq : ∀ message, Emitted setup leaks execution message →
      Emitted setup leaks next message := by
    intro message emitted
    unfold Emitted at emitted ⊢
    rw [inputsEq]
    exact emitted
  obtain ⟨message, emitted, authored, marked | ⟨other, otherEmitted, otherAuthored, different,
    event, named, otherNamed⟩⟩ := doomed
  · exact ⟨message, emittedEq message emitted, authored,
      Or.inl (marked.environment facts reached emitted)⟩
  · exact ⟨message, emittedEq message emitted, authored,
      Or.inr ⟨other, emittedEq other otherEmitted, otherAuthored, different, event, named,
        otherNamed⟩⟩

/-- An accepted emitted envelope carries a valid token and is sent by its
event's actor. -/
theorem SettledFacts.accepted_emitted {execution : (application setup leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks execution message)
    (accepted : (message.id, true) ∈ execution.receipts) :
    message ∈ execution.network.ledger ∧ message.payload.tokenValid = true ∧
      ∃ event, message.payload.call.event? (graph setup) = some event ∧
        (graph setup).actor? event = some message.sender := by
  obtain ⟨witness, member, identified, valid, event, named, _, owned⟩ :=
    facts.accepted message.id accepted
  have same := facts.emitted_unique (facts.carried.ledger witness member) emitted identified
  subst same
  exact ⟨member, valid, event, named, owned⟩

/-- At a settlement that completed every event, a condemned emitted packet is
forbidden by the settled record. -/
theorem Condemned.forbidden {execution : (application setup leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    (terminal : execution.application.config.cut.Terminal)
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks execution message)
    (marked : Condemned setup leaks execution message) :
    ((runtime setup).settledRecord leaks execution).permits message = false := by
  have settledAll : ∀ event, event ∈ ((runtime setup).settledRecord leaks
      execution).view.observation.completionOrder := by
    intro event
    apply (execution.application.config.history_exact event).mpr
    rw [terminal]
    exact Finset.mem_univ event
  have unaccepted : ∀ message event, message.payload.call.event? (graph setup) = some event →
      (message.id, true) ∉ execution.receipts →
      ((runtime setup).settledRecord leaks execution).permits message = false := by
    intro message event named rejected
    exact SettledRecord.permits_eq_false_of_settled _ message event named (settledAll event)
      fun accepted => rejected accepted.1
  have misformed : ∀ message event, message.payload.call.event? (graph setup) = some event →
      ¬ ((runtime setup).settledRecord leaks execution).SettledContent message →
      ((runtime setup).settledRecord leaks execution).permits message = false := by
    intro message event named rejected
    exact SettledRecord.permits_eq_false_of_settled _ message event named (settledAll event)
      fun accepted => rejected accepted.2
  rcases marked with forbidden | ⟨event, named, rejected, _⟩ |
      ⟨_, event, named, _, content⟩
  · cases call : message.payload.call.event? (graph setup) with
    | none => exact SettledRecord.permits_eq_false_of_none _ message call
    | some event =>
        by_cases accepted : (message.id, true) ∈ execution.receipts
        · obtain ⟨_, valid, acceptedEvent, acceptedNamed, owned⟩ :=
            facts.accepted_emitted emitted accepted
          rw [call] at acceptedNamed
          cases Option.some.inj acceptedNamed
          apply misformed message event call
          rcases forbidden with invalid | signed | ⟨foreignEvent, foreignNamed, foreign⟩
          · rw [valid] at invalid
            cases invalid
          · exact signed.not_settledContent _
          · rw [call] at foreignNamed
            cases Option.some.inj foreignNamed
            exact (foreign owned).elim
        · exact unaccepted message event call accepted
  · exact unaccepted message event named rejected
  · exact misformed message event named content

/-- At a settlement that completed every event, a doomed author has an emitted
packet the settled record forbids. -/
theorem Doomed.forbidden {execution : (application setup leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    (terminal : execution.application.config.cut.Terminal) {who : Player}
    (doomed : Doomed setup leaks execution who) :
    ∃ message, Emitted setup leaks execution message ∧ message.sender = who ∧
      ((runtime setup).settledRecord leaks execution).permits message = false := by
  have settledAll : ∀ event, event ∈ ((runtime setup).settledRecord leaks
      execution).view.observation.completionOrder := by
    intro event
    apply (execution.application.config.history_exact event).mpr
    rw [terminal]
    exact Finset.mem_univ event
  have unaccepted : ∀ message event, message.payload.call.event? (graph setup) = some event →
      (message.id, true) ∉ execution.receipts →
      ((runtime setup).settledRecord leaks execution).permits message = false := by
    intro message event named rejected
    exact SettledRecord.permits_eq_false_of_settled _ message event named (settledAll event)
      fun accepted => rejected accepted.1
  have misformed : ∀ message event, message.payload.call.event? (graph setup) = some event →
      ¬ ((runtime setup).settledRecord leaks execution).SettledContent message →
      ((runtime setup).settledRecord leaks execution).permits message = false := by
    intro message event named rejected
    exact SettledRecord.permits_eq_false_of_settled _ message event named (settledAll event)
      fun accepted => rejected accepted.2
  obtain ⟨message, emitted, authored, marked | ⟨other, otherEmitted, otherAuthored, different,
    event, named, otherNamed⟩⟩ := doomed
  · exact ⟨message, emitted, authored, marked.forbidden facts terminal emitted⟩
  · by_cases accepted : (message.id, true) ∈ execution.receipts
    · by_cases otherAccepted : (other.id, true) ∈ execution.receipts
      · have firstLedger := (facts.accepted_emitted emitted accepted).1
        have secondLedger := (facts.accepted_emitted otherEmitted otherAccepted).1
        exact (different (facts.single other secondLedger message firstLedger otherAccepted
          accepted event otherNamed named)).elim
      · exact ⟨other, otherEmitted, otherAuthored, unaccepted other event otherNamed
          otherAccepted⟩
    · exact ⟨message, emitted, authored, unaccepted message event named accepted⟩

/-- A legal history's state: every send-time breach in its traffic dooms the
breach's author. -/
def BreachesDoomed : (application setup leaks).ProtocolState → Prop
  | none => True
  | some control => ∀ record ∈ (application setup leaks).executionTraffic control.execution,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = false →
      Doomed setup leaks control.execution record.envelope.sender

/-- Every send-time breach in the traffic of a legal history dooms its author,
for every scheduler and arbitrary responses. -/
theorem breachesDoomed_history (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) :
    ∀ {state} (_ : ((application setup leaks).protocol initial horizon scheduler).Trace state),
      BreachesDoomed state
  | _, .start => trivial
  | _, .extend (source := before) prior joint _ reached => by
      let app := application setup leaks
      have valid := breachesDoomed_history initial horizon scheduler prior
      cases before with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro record member
          simp [ReactiveApplication.executionTraffic, ReactiveApplication.Execution.initial,
            ReactiveApplication.trafficViews] at member
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          have facts := settledFacts_history initial horizon scheduler prior
          cases actor with
          | some who =>
              have traffic := app.stateTraffic_transition initial horizon scheduler
                ⟨_, prior⟩ joint _ reached
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro record member breach
              change record ∈ app.stateTraffic (some _) at member
              rw [traffic] at member
              rcases List.mem_append.mp member with prior' | fresh
              · exact (valid record prior' breach).respond who _
              · simp only [ReactiveApplication.trafficStep, List.mem_map] at fresh
                obtain ⟨input, inside, rfl⟩ := fresh
                refine doomed_of_breach execution facts who _ input ?_ breach
                exact List.mem_of_mem_drop inside
          | none =>
              cases remaining with
              | zero =>
                  cases (PMF.mem_support_pure_iff _ _).mp reached
                  exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro record member breach
                  have recordsEq := app.executionTraffic_environment execution next command
                    supported
                  change record ∈ app.executionTraffic next at member
                  rw [recordsEq] at member
                  exact (valid record member breach).environment facts supported

/-- **Send-time breaches are settled-record breaches.** At every legal history
whose contract completed every event, under arbitrary responses and
scheduling, the author of a transmission that breaks the send-time conformance
rule is also the signed author of a transmission the settled record forbids. -/
theorem settled_breach_of_sendTime_breach (initial : PMF (application setup leaks).State)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol initial horizon scheduler).Trace
      (some control))
    (terminal : control.execution.application.config.cut.Terminal)
    (record : (application setup leaks).TrafficRecord)
    (present : record ∈ (application setup leaks).executionTraffic control.execution)
    (breach : (runtime setup).permittedServiceEnvelope record.observation record.ledger
      record.envelope = false) :
    ∃ other ∈ (application setup leaks).executionTraffic control.execution,
      other.envelope.sender = record.envelope.sender ∧
      ((runtime setup).settledRecord leaks control.execution).permits other.envelope =
        false := by
  have facts := settledFacts_history initial horizon scheduler trace
  obtain ⟨message, emitted, authored, forbidden⟩ := (breachesDoomed_history initial horizon
    scheduler trace record present breach).forbidden facts terminal
  have inputs := (application setup leaks).stateTraffic_inputs initial horizon scheduler trace
  have inputMember : message ∈ control.execution.network.inputs := emitted
  change ((application setup leaks).executionTraffic control.execution).map
    ReactiveApplication.TrafficRecord.envelope = control.execution.network.inputs at inputs
  rw [← inputs] at inputMember
  obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp inputMember
  exact ⟨other, otherMember, authored, forbidden⟩

/-- A response that submits a packet which the handler rejects at its emission
state, or whose signed content cannot settle, condemns that packet. Evidence
soundness and binding provenance hold at every legal history. -/
theorem condemned_of_unacceptable (execution : (application setup leaks).Execution)
    (facts : SettledFacts setup leaks execution)
    (sound : ((runtime setup).packetEvidence leaks).Sound execution)
    (binding : execution.application.BindingInvariant)
    (who : Player) (material : (application setup leaks).Submission)
    (departure :
      let state := (application setup leaks).submit execution.application who material
      let packet := (application setup leaks).packet state who (execution.network.known who)
        material
      (application setup leaks).handle state
          ⟨(who, execution.network.nextSerial who), packet⟩ = none ∨
        SignedContentBreach (⟨(who, execution.network.nextSerial who), packet⟩ :
          Message Player (WitnessedPacket (graph setup)))) :
    Condemned setup leaks (execution.respond (application setup leaks) who
      ⟨some material⟩)
      ⟨(who, execution.network.nextSerial who),
        (application setup leaks).packet ((application setup leaks).submit
          execution.application who material) who (execution.network.known who) material⟩ := by
  let app := application setup leaks
  let next := execution.respond app who ⟨some material⟩
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(who, execution.network.nextSerial who),
      app.packet (app.submit execution.application who material) who
        (execution.network.known who) material⟩
  have after := settledFacts_respond execution facts who ⟨some material⟩
  have soundNext := ((runtime setup).packetEvidence leaks).sound_respond execution who
    ⟨some material⟩ sound
  have bindingNext : next.application.BindingInvariant :=
    ((runtime setup).reactiveBindingInvariant leaks).respond execution who _ binding
  have pendingNext : message ∈ next.network.pending :=
    List.mem_append_right execution.network.pending (List.mem_singleton_self _)
  have emitted : Emitted setup leaks next message :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have unaccepted : (message.id, true) ∉ next.receipts := by
    intro accepted
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp (after.receipt_published accepted)
    have bound := after.serials.ledger other otherMember
    change other.id.2 < next.network.nextSerial other.id.1 at bound
    rw [same] at bound
    change execution.network.nextSerial who < next.network.nextSerial who at bound
    have unchanged : next.network.ledger = execution.network.ledger :=
      app.respond_ledger execution who _
    rw [unchanged] at otherMember
    have old := facts.serials.ledger other otherMember
    rw [same] at old
    exact Nat.lt_irrefl _ old
  by_cases forbidden : ContentForbidden setup message
  · exact Or.inl forbidden
  have valid : message.payload.tokenValid = true := by
    by_contra invalid
    exact forbidden (Or.inl (Bool.eq_false_iff.mpr invalid))
  obtain ⟨event, named, tokenEq⟩ := (WitnessedPacket.tokenValid_iff message.payload).mp valid
  have settled := after.issued message emitted ⟨event⟩ tokenEq
  by_cases done : event ∈ next.application.config.cut.completed
  · exact Or.inr (Or.inl ⟨event, named, unaccepted, Or.inl done⟩)
  have ready : next.application.config.cut.Ready event :=
    ⟨done, fun predecessor member => settled predecessor member⟩
  by_cases conditions : PublicConditions setup next.application message.payload.call
  swap
  · exact Or.inr (Or.inl ⟨event, named, unaccepted, Or.inr ⟨ready, Or.inl conditions⟩⟩)
  by_cases fails : ContentFails setup next.application message
  · exact Or.inr (Or.inl ⟨event, named, unaccepted, Or.inr ⟨ready, Or.inr fails⟩⟩)
  exfalso
  have fresh := fresh_of_conditions next.application message event named forbidden ready
    conditions fails
  have timely : next.application.WithinDeadline (runtime setup) event := by
    rcases message with ⟨id, ⟨call, evidence, token⟩⟩
    cases call with
    | commitment actual candidate =>
        change some actual = some event at named
        cases Option.some.inj named
        exact conditions.1
    | opening actual candidate raw =>
        change some actual = some event at named
        cases Option.some.inj named
        exact conditions.1
    | withhold actual =>
        change some actual = some event at named
        cases Option.some.inj named
        exact conditions.1
    | malformed raw => cases named
  rcases departure with rejected | uncertified
  · obtain ⟨accepted, handled⟩ := (runtime setup).freshServiceAcceptable_accepted
      next.application next.application.publicView message
      (EventGraphRuntime.freshServiceEnvelope.acceptable (runtime setup) fresh) rfl rfl event
      named timely (fun fact member => soundNext.pending message pendingNext fact member)
      bindingNext
    have reactive : app.handle next.application message = some accepted := by
      rw [reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _ valid]
      exact handled
    change app.handle next.application message = none at rejected
    rw [rejected] at reactive
    cases reactive
  · exact forbidden (Or.inr (Or.inl uncertified))

variable (setup leaks) in
/-- A packet stays condemned along with the settled facts. -/
def CondemnedFacts (message : Message Player (WitnessedPacket (graph setup)))
    (execution : (application setup leaks).Execution) : Prop :=
  SettledFacts setup leaks execution ∧ Emitted setup leaks execution message ∧
    Condemned setup leaks execution message

/-- Condemnation persists under every response and scheduler command. -/
theorem condemnedFacts_persistent (message : Message Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy) :
    (application setup leaks).PolicyInvariant players (CondemnedFacts setup leaks message) where
  respond execution who action held _ :=
    ⟨settledFacts_respond execution held.1 who action,
      respond_emitted_mono execution who action held.2.1, held.2.2.respond who action⟩
  environment execution next command held reached := by
    obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
    refine ⟨settledFacts_environment execution next command held.1 reached, ?_,
      held.2.2.environment held.1 reached held.2.1⟩
    unfold Emitted
    rw [inputsEq]
    exact held.2.1

end Marks

end Vegas
