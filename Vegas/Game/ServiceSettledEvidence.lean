/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterAsync
import Vegas.Pending.ReactiveSettledStability
import Vegas.Pending.ReactiveServiceAudit
import Vegas.Pending.ReactiveFreshCallAcceptance
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.ReactiveAssociationEvidence
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveTrafficContinuation
import Vegas.Pending.ReactiveEventStability

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
  event, opening evidence on a commitment, an opening
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
  {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- An envelope the network has carried as an input. -/
def Emitted (execution : (serviceApplication setup mode deadline leaks).Execution)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  message ∈ execution.network.inputs

/-- One scheduler command keeps the inputs and the next serials. It either keeps
the ledger and receipts and lets the network only learn, or includes one pending
envelope with its receipt. -/
theorem environmentStep_shape
    (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (command : (serviceApplication setup mode deadline leaks).Command)
    (reached : next ∈
        (execution.environmentStep (serviceApplication setup mode deadline leaks)
        command).support) : next.network.inputs = execution.network.inputs ∧
    next.network.nextSerial = execution.network.nextSerial ∧
    ((next.receipts = execution.receipts ∧ next.network.ledger = execution.network.ledger ∧ ∀ safe :
        Message Player (WitnessedPacket (serviceGraph setup mode)) → Prop,
        execution.network.Satisfies safe → next.network.Satisfies safe) ∨ ∃ id message,
        execution.network.lookup id = some message ∧ next.network =
        (execution.network.includePending id).2 ∧ next.receipts = execution.receipts ++
        [(id, ((serviceApplication setup mode deadline leaks).handle execution.application
        message).isSome)] ∧ next.application =
        ((serviceApplication setup mode deadline leaks).handle execution.application
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
      change
          (execution.includePending (serviceApplication setup mode deadline leaks)
              id).network.inputs = _ ∧
          (execution.includePending (serviceApplication setup mode deadline leaks)
              id).network.nextSerial = _ ∧
          (((execution.includePending (serviceApplication setup mode deadline leaks) id).receipts =
              _ ∧ (execution.includePending (serviceApplication setup mode deadline leaks)
              id).network.ledger = _ ∧ _) ∨ _)
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid⟩⟩
      | some message =>
          refine ⟨rfl, rfl, Or.inr ⟨id, message, found, ?_, rfl, rfl⟩⟩
          simp only [found]

/-- The facts every legal history keeps, for every scheduler and arbitrary
responses, that tie the receipts and tokens to the traffic. -/
structure SettledFacts (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop where
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  receipts : execution.ReceiptsSound (serviceApplication setup mode deadline leaks) (fun _ => True)
  /-- Every envelope the network holds was an input. -/
  carried : execution.network.Satisfies (Emitted setup leaks execution)
  /-- Every allocated identifier was emitted. -/
  allocated : ∀ who serial, serial < execution.network.nextSerial who →
    ∃ message, Emitted setup leaks execution message ∧ message.id = (who, serial)
  /-- A readiness token names an event whose prerequisites have completed. -/
  issued : ∀ message, Emitted setup leaks execution message → ∀ token,
    message.payload.token = some token →
    ∀ predecessor ∈ (serviceGraph setup mode).order.predecessors token.event,
      predecessor ∈ execution.application.config.cut.completed
  /-- An accepting receipt names a ledger envelope with a valid token, whose
  event has completed and whose sender is that event's actor. -/
  accepted : ∀ id, (id, true) ∈ execution.receipts →
    ∃ message ∈ execution.network.ledger, message.id = id ∧
      message.payload.tokenValid = true ∧
      ∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
        event ∈ execution.application.config.cut.completed ∧
        (serviceGraph setup mode).actor? event = some message.sender
  /-- The contract accepts at most one identifier per event. -/
  single : ∀ first ∈ execution.network.ledger, ∀ second ∈ execution.network.ledger,
    (first.id, true) ∈ execution.receipts → (second.id, true) ∈ execution.receipts →
    ∀ event, first.payload.call.event? (serviceGraph setup mode) = some event →
      second.payload.call.event? (serviceGraph setup mode) = some event → first.id = second.id
  /-- Once a later identifier of an author is accepted, the event of each of the
  author's earlier identifiers with a valid token for an event the author acts
  at has completed. -/
  ordered : ∀ earlier later, Emitted setup leaks execution earlier →
    Emitted setup leaks execution later → earlier.sender = later.sender →
    earlier.id.2 < later.id.2 → (later.id, true) ∈ execution.receipts →
    earlier.payload.tokenValid = true →
    ∀ event, earlier.payload.call.event? (serviceGraph setup mode) = some event →
      (serviceGraph setup mode).actor? event = some earlier.sender →
      event ∈ execution.application.config.cut.completed

variable {setup leaks}

/-- A receipt names an identifier on the ledger. -/
theorem SettledFacts.receipt_published
    {execution : (serviceApplication setup mode deadline leaks).Execution}
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
theorem SettledFacts.emitted_unique
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {first second : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (firstEmitted : Emitted setup leaks execution first)
    (secondEmitted : Emitted setup leaks execution second) (same : first.id = second.id) :
    first = second := by
  exact ((facts.unique.inputs first firstEmitted).inputs second secondEmitted
    same.symm).symm

/-- An emitted envelope's serial is below its author's next serial. -/
theorem SettledFacts.emitted_serial
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message) :
    message.id.2 < execution.network.nextSerial message.id.1 := by
  exact facts.serials.inputs message emitted

theorem settledFacts_initial (state : (serviceApplication setup mode deadline leaks).State) :
    SettledFacts setup leaks
        (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
      state) where
  serials := MessageNetwork.SerialsBeforeNext.empty
  unique := MessageNetwork.UniqueIds.empty
  receipts := (serviceApplication setup mode deadline leaks).receiptsSound_initial _ state
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
theorem respond_emitted_mono (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) (action : (serviceApplication setup mode deadline leaks).Action)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message) :
    Emitted setup leaks
        (execution.respond (serviceApplication setup mode deadline leaks) who action) message := by
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
theorem respond_emitted {execution : (serviceApplication setup mode deadline leaks).Execution}
    (_facts : SettledFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (emitted : Emitted setup leaks
        (execution.respond (serviceApplication setup mode deadline leaks) who action) message) :
    Emitted setup leaks execution message ∨
      ∃ material, action.transmission = some material ∧
        message = ⟨(who, execution.network.nextSerial who),
          (serviceApplication setup mode deadline leaks).packet
          ((serviceApplication setup mode deadline leaks).submit
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
theorem respond_nextSerial (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) (action : (serviceApplication setup mode deadline leaks).Action)
    (observer : Player) :
    (execution.respond (serviceApplication setup mode deadline leaks) who action).network.nextSerial
    observer = execution.network.nextSerial observer ∨
    ((∃ material, action.transmission = some material) ∧ observer = who ∧
        (execution.respond (serviceApplication setup mode deadline leaks) who
        action).network.nextSerial observer =
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
theorem packet_token_issued (state : (serviceApplication setup mode deadline leaks).State)
    (who : Player) (known : List (Message Player (WitnessedPacket (serviceGraph setup mode))))
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (token : ReadinessToken (serviceGraph setup mode))
    (carried :
        ((serviceApplication setup mode deadline leaks).packet
        ((serviceApplication setup mode deadline leaks).submit state who material) who known
        material).token = some token) : ∀ predecessor ∈ (serviceGraph setup mode).order.predecessors
    token.event,
      predecessor ∈ state.config.cut.completed := by
  rw [reactiveApplication_packet_token] at carried
  unfold PublicView.tokenFor at carried
  obtain ⟨event, _, issued⟩ := Option.bind_eq_some_iff.mp carried
  obtain ⟨rfl, settled⟩ := (state.publicView.readinessToken?_eq_some_iff event token).mp issued
  intro predecessor member
  exact (state.config.history_exact predecessor).mp (settled predecessor member)

theorem settledFacts_respond (execution : (serviceApplication setup mode deadline leaks).Execution)
    (facts : SettledFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action) :
    SettledFacts setup leaks
        (execution.respond (serviceApplication setup mode deadline leaks) who action) := by
  let app := serviceApplication setup mode deadline leaks
  have configEq :=
      ((serviceRuntime setup mode deadline).reactive_respond_application leaks execution who
          action).1
  have receiptsEq := app.respond_receipts execution who action
  have ledgerEq := app.respond_ledger execution who action
  have identity := (app.messageIdentityInvariant (fun _ _ => PMF.pure .wait)).respond execution
    who action ⟨facts.serials, facts.unique⟩
  have fresh : ∀ material (token : ReadinessToken (serviceGraph setup mode)),
      (app.packet (app.submit execution.application who material) who
        (execution.network.known who) material).token = some token →
      ∀ predecessor ∈ (serviceGraph setup mode).order.predecessors token.event,
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
theorem includePending_found
    (network : MessageNetwork Player (WitnessedPacket (serviceGraph setup mode)))
    (id : MessageId Player) (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (found : network.lookup id = some message) : message.id = id ∧ message ∈ network.pending ∧
      (network.includePending id).2.ledger = network.ledger ++ [message] := by
  refine ⟨?_, List.mem_of_find?_eq_some found, ?_⟩
  · have identified := (List.find?_eq_some_iff_append.mp found).1
    simpa only [decide_eq_true_eq] using identified
  · simp only [MessageNetwork.includePending, found]

/-- What an accepting inclusion establishes: the envelope's token is valid, its
event was ready and has completed, and its sender is the event's actor. -/
theorem accepted_inclusion (state next : (serviceApplication setup mode deadline leaks).State)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (handled : (serviceApplication setup mode deadline leaks).handle state message = some next) :
    message.payload.tokenValid = true ∧
      ∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
        state.config.cut.Ready event ∧ event ∈ next.config.cut.completed ∧
        (serviceGraph setup mode).actor? event = some message.sender := by
  obtain ⟨valid, call⟩ := reactiveApplication_handle_eq_some (serviceRuntime setup mode deadline)
      leaks state next message handled
  obtain ⟨event, named, ready, action, member⟩ :=
    handle_config_mem_step (serviceRuntime setup mode deadline) state next _ call
  refine
      ⟨valid, event, named, ready, ?_, handle_sender_actor (serviceRuntime setup mode deadline)
          state next _ call event named⟩
  rw [state.config.step_cut event ready action next.config member]
  exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)

theorem settledFacts_environment
    (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (command : (serviceApplication setup mode deadline leaks).Command)
    (facts : SettledFacts setup leaks execution)
    (reached : next ∈
        (execution.environmentStep (serviceApplication setup mode deadline leaks)
        command).support) :
    SettledFacts setup leaks next := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨inputsEq, serialEq, effect⟩ :=
    environmentStep_shape setup leaks execution next command reached
  have step := contractStep_environment (serviceRuntime setup mode deadline) leaks execution next
      command reached
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
      have readyFresh : ∀ (other : Message Player (WitnessedPacket (serviceGraph setup mode))),
          other ∈ execution.network.ledger → (other.id, true) ∈ execution.receipts →
          other.payload.call.event? (serviceGraph setup mode) = some event →
          (app.handle execution.application message).isSome = true →
          message.payload.call.event? (serviceGraph setup mode) = some event → False := by
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
      named owned
    rcases effect with ⟨receiptsEq, _, _⟩ |
        ⟨id, message, found, networkEq, receiptsEq, applicationEq⟩
    · rw [receiptsEq] at accepted
      exact completedMono event (facts.ordered earlier later ((emittedEq earlier).mp
        earlierEmitted) ((emittedEq later).mp laterEmitted) sameSender lower accepted valid
          event named owned)
    · rw [receiptsEq] at accepted
      rcases List.mem_append.mp accepted with prior | fresh
      · exact completedMono event (facts.ordered earlier later ((emittedEq earlier).mp
          earlierEmitted) ((emittedEq later).mp laterEmitted) sameSender lower prior valid
            event named owned)
      · obtain ⟨identified, isSome⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
        obtain ⟨after, handled⟩ := Option.isSome_iff_exists.mp isSome.symm
        obtain ⟨_, accepted', _, ready, completed, actor⟩ :=
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
          have senders : message.sender = earlier.sender := by
            obtain ⟨messageId, _, _⟩ := includePending_found execution.network id message found
            change message.id.1 = earlier.id.1
            rw [messageId, ← identified]
            exact sameSender.symm
          cases (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
            execution.application.config.cut readyEarlier ready owned (actor.trans
              (congrArg some senders))
          rw [applicationEq, handled]
          exact completed

theorem settledFacts_serviceInvariant
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) :
    (serviceApplication setup mode deadline leaks).ServiceInvariant scheduler
    (SettledFacts setup leaks) where
  respond execution who action facts := settledFacts_respond execution facts who action
  environment execution next command facts _ reached :=
    settledFacts_environment execution next command facts reached

/-- The settled facts hold at every legal history, for every scheduler and
arbitrary responses. -/
theorem settledFacts_history (initial : PMF (serviceApplication setup mode deadline leaks).State)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol initial horizon scheduler).Trace
        (some control)) : SettledFacts setup leaks control.execution :=
    (settledFacts_serviceInvariant scheduler).history initial horizon
    (fun state _ => settledFacts_initial state) trace

end Facts

section Sequential

/-- Two ready events of the sequentialized graph are equal. -/
theorem ready_unique {setup : Setup (Player := Player) (L := L)} (cut : (graph setup).order.Cut)
    {first second : (graph setup).EventId}
    (firstReady : cut.Ready first) (secondReady : cut.Ready second) : first = second :=
  setup.eventGraph.sequentialize_ready_unique cut firstReady secondReady

end Sequential

section Marks

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))


/-- The packet's content alone rules it out at every settlement. -/
def ContentForbidden (message : Message Player (WitnessedPacket
    (serviceGraph setup mode))) : Prop :=
  message.payload.tokenValid = false ∨
    message.payload.call.event? (serviceGraph setup mode) = none ∨
    (∃ event candidate, message.payload.call = .commitment event candidate ∧
      message.payload.evidence ≠ none) ∨
    (∃ event candidate raw, message.payload.call = .opening event candidate raw ∧
      certifiedOpening message.payload = false) ∨
    (∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
      (serviceGraph setup mode).actor? event ≠ some message.sender)

/-- The handler's public conditions on a call, other than readiness and the
sender's authority. -/
def PublicConditions (deadline : (serviceGraph setup mode).EventId → Nat)
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (call : Payload (serviceGraph setup mode)) : Prop :=
  match call with
  | .commitment event candidate =>
      state.WithinDeadline (serviceRuntime setup mode deadline) event ∧
        match nodeView (serviceGraph setup mode) event with
        | .bind owner _ _ _ => candidate.1 = owner ∧ state.accepted (.inr event) = none ∧
            state.HandleUnused candidate
        | .resolve .. | .sample .. => False
  | .opening event candidate raw =>
      state.WithinDeadline (serviceRuntime setup mode deadline) event ∧
        match nodeView (serviceGraph setup mode) event with
        | .resolve owner payload binding _ _ _ => candidate.1 = owner ∧
            state.accepted binding.field = some candidate ∧ raw.ty = payload
        | .bind .. | .sample .. => False
  | .malformed _ => True

/-- Accepting the packet at this state would settle content the record
rejects: a commitment to another handle than the author's next prepared one, or
an opening whose guards reject the value. -/
def ContentFails (state : EventGraphRuntime.State (serviceGraph setup mode))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  match message.payload.call with
  | .commitment _ candidate =>
      candidate ≠ (message.sender, .prepared (state.publicView.bindingCount message.sender))
  | .opening _ _ _ => state.publicView.openingGuardsAccepted message.payload = false
  | .malformed _ => False

/-- A packet the settled record forbids at every complete settlement after
this execution: its content is ruled out; or it is not accepted, and either its
event has completed, or its event is ready and the handler cannot accept it
before the event completes, or the record will reject its content if it does;
or it is accepted with content the record rejects. -/
def Condemned (execution : (serviceApplication setup mode deadline leaks).Execution)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  ContentForbidden setup message ∨
    (∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
      (message.id, true) ∉ execution.receipts ∧
      (event ∈ execution.application.config.cut.completed ∨
        (execution.application.config.cut.Ready event ∧
          (¬ PublicConditions setup deadline execution.application message.payload.call ∨
            ContentFails setup execution.application message)))) ∨
    ((message.id, true) ∈ execution.receipts ∧
      ∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
        event ∈ execution.application.config.cut.completed ∧
        ¬ ((serviceRuntime setup mode deadline).settledRecord leaks execution).SettledContent
            message)

/-- Some packet of `who` is forbidden at every complete settlement after this
execution: one is condemned, or two of its identifiers address one event. -/
def Doomed (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) : Prop :=
  ∃ message, Emitted setup leaks execution message ∧ message.sender = who ∧
    (Condemned setup leaks execution message ∨
      ∃ other, Emitted setup leaks execution other ∧ other.sender = who ∧
        other.id ≠ message.id ∧ ∃ event, message.payload.call.event? (serviceGraph setup mode) =
            some event ∧
          other.payload.call.event? (serviceGraph setup mode) = some event)

variable {setup leaks}

/-- An accepting inclusion met the handler's public conditions. -/
theorem handle_publicConditions (state next : EventGraphRuntime.State (serviceGraph setup mode))
    (id : MessageId Player) (call : Payload (serviceGraph setup mode))
    (accepted : handle (serviceRuntime setup mode deadline) state ⟨id, call⟩ = some next) :
    PublicConditions setup deadline state call := by
  classical
  cases call with
  | malformed raw => trivial
  | commitment event candidate =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline (serviceRuntime setup mode deadline) event
        · refine ⟨timely, ?_⟩
          cases view : nodeView (serviceGraph setup mode) event with
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
      · by_cases timely : state.WithinDeadline (serviceRuntime setup mode deadline) event
        · refine ⟨timely, ?_⟩
          cases view : nodeView (serviceGraph setup mode) event with
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
theorem fresh_of_conditions (state : EventGraphRuntime.State (serviceGraph setup mode))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) (event :
        (serviceGraph setup mode).EventId)
    (named : message.payload.call.event? (serviceGraph setup mode) = some event)
    (allowed : ¬ ContentForbidden setup message) (ready : state.config.cut.Ready event)
    (conditions : PublicConditions setup deadline state message.payload.call)
    (content : ¬ ContentFails setup state message) :
    (serviceRuntime setup mode deadline).freshServiceEnvelope state.publicView message := by
  have valid : message.payload.tokenValid = true := by
    by_contra invalid
    exact allowed (Or.inl (Bool.eq_false_iff.mpr invalid))
  have owned : (serviceGraph setup mode).actor? event = some message.sender := by
    by_contra foreign
    exact allowed (Or.inr (Or.inr (Or.inr (Or.inr ⟨event, named, foreign⟩))))
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
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      have empty : evidence = none := by
        by_contra present
        exact allowed (Or.inr (Or.inr (Or.inl ⟨event, candidate, rfl, present⟩)))
      have canonical : candidate = (id.1, .prepared (state.publicView.bindingCount id.1)) := by
        by_contra other
        exact content other
      refine ((serviceRuntime setup mode deadline).freshServiceEnvelope_binding_iff
          state.publicView id event
        candidate evidence (some ⟨event⟩)).mpr ⟨?_, canonical, empty, rfl⟩
      obtain ⟨timely, rest⟩ := conditions
      refine ⟨readyView, timely, ?_⟩
      cases view : nodeView (serviceGraph setup mode) event with
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
            WitnessedPacket (serviceGraph setup mode)) = true := by
        by_contra uncertified
        exact allowed (Or.inr (Or.inr (Or.inr (Or.inl ⟨event, candidate, raw, rfl,
          Bool.eq_false_iff.mpr uncertified⟩))))
      have guarded : state.publicView.openingGuardsAccepted
          ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩ = true := by
        by_contra rejected
        exact content (Bool.eq_false_iff.mpr rejected)
      obtain ⟨timely, rest⟩ := conditions
      cases view : nodeView (serviceGraph setup mode) event with
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [view] at rest
          obtain ⟨handleOwner, associated, typed⟩ := rest
          have authored : id.1 = owner := by
            have actor := nodeView_resolve_actor outputEq codeEq
            rw [owned] at actor
            exact Option.some.inj actor
          exact ((serviceRuntime setup mode deadline).freshServiceEnvelope_opening_iff
              state.publicView id event
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
theorem doomed_of_breach (execution : (serviceApplication setup mode deadline leaks).Execution)
    (facts : SettledFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (emitted : Emitted setup leaks (execution.respond
        (serviceApplication setup mode deadline leaks) who action)
      message)
    (breach :
        (serviceRuntime setup mode deadline).permittedServiceEnvelope
            execution.application.publicView
      execution.network.ledger message = false) :
    Doomed setup leaks (execution.respond (serviceApplication setup mode deadline leaks) who action)
      message.sender := by
  classical
  have after := settledFacts_respond execution facts who action
  have publicEq : (execution.respond
      (serviceApplication setup mode deadline leaks) who action).application.publicView =
      execution.application.publicView :=
    ((serviceRuntime setup mode deadline).reactive_respond_application leaks execution who action).2
  have ledgerEq : (execution.respond
      (serviceApplication setup mode deadline leaks) who action).network.ledger =
      execution.network.ledger :=
          (serviceApplication setup mode deadline leaks).respond_ledger execution who action
  generalize execution.respond (serviceApplication setup mode deadline leaks) who action = next at *
  have unpublished : message.id ∉ next.network.ledger.map Message.id := by
    intro published
    rw [ledgerEq] at published
    rw [(serviceRuntime setup mode deadline).permittedServiceEnvelope_published _ _ _ published]
        at breach
    cases breach
  have unaccepted : (message.id, true) ∉ next.receipts :=
    fun accepted => unpublished (after.receipt_published accepted)
  by_cases forbidden : ContentForbidden setup message
  · exact ⟨message, emitted, rfl, Or.inl (Or.inl forbidden)⟩
  -- A different identifier of the author, not accepted, dooms the author.
  have doomedBy : ∀ other, Emitted setup leaks next other → other.sender = message.sender →
      other.id ≠ message.id → (other.id, true) ∉ next.receipts →
      ∀ event, message.payload.call.event? (serviceGraph setup mode) = some event →
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
      have messageOwned : (serviceGraph setup mode).actor? event = some message.sender := by
        by_contra foreign
        exact forbidden (Or.inr (Or.inr (Or.inr (Or.inr ⟨event, named, foreign⟩))))
      have otherOwned : (serviceGraph setup mode).actor? otherEvent = some message.sender := by
        by_contra foreign
        exact otherForbidden (Or.inr (Or.inr (Or.inr (Or.inr ⟨otherEvent, otherNamed, by
          rw [otherSender]
          exact foreign⟩))))
      cases (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
        next.application.config.cut ready otherReady messageOwned otherOwned
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
  by_cases conditions : PublicConditions setup deadline next.application message.payload.call
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
    rw [((serviceRuntime setup mode deadline).permittedServiceEnvelope_iff _ _ _).mpr (Or.inr
        ⟨serial, fresh⟩)]
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
        valid event named (by
          by_contra foreign
          exact forbidden (Or.inr (Or.inr (Or.inr (Or.inr ⟨event, named, foreign⟩))))))).elim
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

/-- The handler's conditions name an event with an actor. -/
theorem publicConditions_actor (state : EventGraphRuntime.State (serviceGraph setup mode))
    (call : Payload (serviceGraph setup mode)) (event : (serviceGraph setup mode).EventId)
    (named : call.event? (serviceGraph setup mode) = some event)
    (holds : PublicConditions setup deadline state call) :
    ((serviceGraph setup mode).actor? event).isSome = true := by
  cases call with
  | malformed raw => cases named
  | commitment actual candidate =>
      have sameEvent : actual = event := Option.some.inj named
      subst sameEvent
      obtain ⟨_, rest⟩ := holds
      cases view : nodeView (serviceGraph setup mode) actual with
      | bind owner payload outputEq codeEq =>
          rw [nodeView_bind_actor outputEq codeEq]
          rfl
      | resolve _ _ _ _ _ _ => simp only [view] at rest
      | sample _ _ _ _ => simp only [view] at rest
  | opening actual candidate raw =>
      have sameEvent : actual = event := Option.some.inj named
      subst sameEvent
      obtain ⟨_, rest⟩ := holds
      cases view : nodeView (serviceGraph setup mode) actual with
      | resolve owner payload binding checks outputEq codeEq =>
          rw [nodeView_resolve_actor outputEq codeEq]
          rfl
      | bind _ _ _ _ => simp only [view] at rest
      | sample _ _ _ _ => simp only [view] at rest

/-- The handler's public conditions only weaken as the clock advances. -/
theorem publicConditions_of_later (first second : EventGraphRuntime.State (serviceGraph setup mode))
    (acceptedEq : second.accepted = first.accepted)
    (activatedEq : second.activatedAt = first.activatedAt)
    (clockLe : first.clock ≤ second.clock) (call : Payload (serviceGraph setup mode))
    (holds : PublicConditions setup deadline second call) : PublicConditions setup deadline first
        call := by
  have timely : ∀ event, second.WithinDeadline (serviceRuntime setup mode deadline) event →
      first.WithinDeadline (serviceRuntime setup mode deadline) event := by
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
  | commitment event candidate =>
      obtain ⟨within, rest⟩ := holds
      refine ⟨timely event within, ?_⟩
      cases view : nodeView (serviceGraph setup mode) event with
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
      cases view : nodeView (serviceGraph setup mode) event with
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [view] at rest ⊢
          obtain ⟨handleOwner, associated, typed⟩ := rest
          exact ⟨handleOwner, acceptedEq ▸ associated, typed⟩
      | bind _ _ _ _ => simp only [view] at rest
      | sample _ _ _ _ => simp only [view] at rest

/-- The settled content of a packet for a completed event is fixed by every
later contract step. -/
theorem settledContent_of_step {before after : EventGraphRuntime.State (serviceGraph setup mode)}
    (step : ContractStep before after)
    (beforeReceipts afterReceipts : List (MessageId Player × Bool))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) (event :
        (serviceGraph setup mode).EventId)
    (named : message.payload.call.event? (serviceGraph setup mode) = some event)
    (completed : event ∈ before.config.cut.completed)
    (content : (⟨after.publicView, afterReceipts⟩ : SettledRecord
        (serviceGraph setup mode)).SettledContent
      message) :
    (⟨before.publicView, beforeReceipts⟩ : SettledRecord
        (serviceGraph setup mode)).SettledContent message := by
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
theorem newly_accepted {execution next : (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
    (facts : SettledFacts setup leaks execution)
    (reached : next ∈
        (execution.environmentStep (serviceApplication setup mode deadline leaks) command).support)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message)
    (before : (message.id, true) ∉ execution.receipts)
    (after : (message.id, true) ∈ next.receipts) :
    ∃ state, (serviceApplication setup mode deadline leaks).handle execution.application message =
        some state ∧
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
theorem Condemned.respond {execution : (serviceApplication setup mode deadline leaks).Execution}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (marked : Condemned setup leaks execution message) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action) :
    Condemned setup leaks (execution.respond
        (serviceApplication setup mode deadline leaks) who action) message := by
  obtain ⟨configEq, publicEq⟩ :=
      (serviceRuntime setup mode deadline).reactive_respond_application leaks execution
    who action
  have receiptsEq :=
      (serviceApplication setup mode deadline leaks).respond_receipts execution who action
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
theorem Doomed.respond {execution : (serviceApplication setup mode deadline leaks).Execution}
    {owner : Player}
    (doomed : Doomed setup leaks execution owner) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action) :
    Doomed setup leaks (execution.respond
        (serviceApplication setup mode deadline leaks) who action) owner := by
  obtain ⟨message, emitted, authored, marked | ⟨other, otherEmitted, otherAuthored, different,
    event, named, otherNamed⟩⟩ := doomed
  · exact ⟨message, respond_emitted_mono execution who action emitted, authored,
      Or.inl (marked.respond who action)⟩
  · exact ⟨message, respond_emitted_mono execution who action emitted, authored,
      Or.inr ⟨other, respond_emitted_mono execution who action otherEmitted, otherAuthored,
        different, event, named, otherNamed⟩⟩

/-- Every ready event with an actor carries its activation time. -/
def ActivationKept (state : EventGraphRuntime.State (serviceGraph setup mode)) : Prop :=
  ∀ event, state.config.cut.Ready event → ((serviceGraph setup mode).actor? event).isSome = true →
    (state.activatedAt event).isSome = true

/-- A refreshed activation table keeps every ready actor event activated. -/
theorem activationKept_refresh (state : EventGraphRuntime.State (serviceGraph setup mode))
    {clock : Nat} {prior : (serviceGraph setup mode).EventId → Option Nat}
    (refreshed : state.activatedAt = EventGraphRuntime.State.refreshActivated state.config
      clock prior) : ActivationKept state := by
  intro event ready actor
  obtain ⟨owner, owned⟩ := Option.isSome_iff_exists.mp actor
  rw [refreshed]
  simp only [EventGraphRuntime.State.refreshActivated, ready, ↓reduceDIte, owned]
  cases prior event <;> rfl

/-- Initial states keep every ready actor event activated. -/
theorem activationKept_initial (inputs : (serviceGraph setup mode).Inputs) :
    ActivationKept (EventGraphRuntime.State.initial inputs) :=
  activationKept_refresh _ rfl

variable (setup leaks) in
/-- Every operation of the application keeps every ready actor event
activated. -/
theorem activationKeptInvariant :
    (serviceApplication setup mode deadline leaks).Invariant ActivationKept where
  submit state who material kept := by
    have publicEq := (serviceRuntime setup mode deadline).reactiveApplication_submit_publicView
      leaks state who material
    have activatedEq : ((serviceApplication setup mode deadline leaks).submit state who
        material).activatedAt = state.activatedAt :=
      congrArg PublicView.activatedAt publicEq
    have configEq : ((serviceApplication setup mode deadline leaks).submit state who
        material).config = state.config := by
      change (submitStep _ who _).config = _
      rw [submitStep_config]
      exact (Submission.register_facts material.call who state).1
    intro event ready actor
    rw [activatedEq]
    exact kept event (configEq ▸ ready) actor
  handle state message next kept accepted :=
    activationKept_refresh next (handle_clock_activated (serviceRuntime setup mode deadline)
      state next _ (reactiveHandle_call accepted)).2
  environment state command next kept reached := by
    replace reached : next ∈ (EventGraphRuntime.environmentStep
      (serviceRuntime setup mode deadline) state command).support := reached
    cases command with
    | advanceClock =>
        simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at reached
        subst next
        exact kept
    | executeSample sampled =>
        rcases (environmentStep_executeSample_config_activated
          (serviceRuntime setup mode deadline) state next sampled reached).2 with
          ⟨configEq, activatedEq⟩ | ⟨_, _, _, activatedEq⟩
        · intro event ready actor
          rw [activatedEq]
          exact kept event (configEq ▸ ready) actor
        · exact activationKept_refresh next activatedEq
    | expire expired =>
        rcases (environmentStep_expire_config_activated (serviceRuntime setup mode deadline)
          state next expired reached).2 with ⟨configEq, activatedEq⟩ | ⟨_, _, _, activatedEq⟩
        · intro event ready actor
          rw [activatedEq]
          exact kept event (configEq ▸ ready) actor
        · exact activationKept_refresh next activatedEq

/-- A response keeps every ready actor event activated. -/
theorem activationKept_respond (execution :
    (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) (action : (serviceApplication setup mode deadline leaks).Action)
    (kept : ActivationKept execution.application) :
    ActivationKept (execution.respond (serviceApplication setup mode deadline leaks) who
      action).application := by
  obtain ⟨configEq, publicEq⟩ := (serviceRuntime setup mode deadline).reactive_respond_application
    leaks execution who action
  have activatedEq : (execution.respond (serviceApplication setup mode deadline leaks) who
      action).application.activatedAt = execution.application.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  intro event ready actor
  rw [activatedEq]
  exact kept event (configEq ▸ ready) actor

/-- What one scheduler command can do to the handler's conditions: the clock
only advances; an activated actor event that stays ready keeps its activation
time; and an accepted handle appears only at a previously vacant field of an
event that was ready. -/
theorem environmentStep_handlerTables
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
    (reached : next ∈ (execution.environmentStep
        (serviceApplication setup mode deadline leaks) command).support) :
    execution.application.clock ≤ next.application.clock ∧
      (∀ event, next.application.config.cut.Ready event →
        ((serviceGraph setup mode).actor? event).isSome = true →
        (execution.application.activatedAt event).isSome = true →
        next.application.activatedAt event = execution.application.activatedAt event) ∧
      (∀ field, next.application.accepted field = execution.application.accepted field ∨
        (execution.application.accepted field = none ∧
          ∃ event, field = .inr event ∧ execution.application.config.cut.Ready event)) ∧
      (ActivationKept execution.application → ActivationKept next.application) := by
  classical
  let Tables (state : EventGraphRuntime.State (serviceGraph setup mode)) : Prop :=
    execution.application.clock ≤ state.clock ∧
      (∀ event, state.config.cut.Ready event →
        ((serviceGraph setup mode).actor? event).isSome = true →
        (execution.application.activatedAt event).isSome = true →
        state.activatedAt event = execution.application.activatedAt event) ∧
      (∀ field, state.accepted field = execution.application.accepted field ∨
        (execution.application.accepted field = none ∧
          ∃ event, field = .inr event ∧ execution.application.config.cut.Ready event)) ∧
      (ActivationKept execution.application → ActivationKept state)
  have unchanged : Tables execution.application :=
    ⟨le_refl _, fun _ _ _ _ => rfl, fun _ => Or.inl rfl, id⟩
  have refreshed (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (ready : config.cut.Ready event)
      (actor : ((serviceGraph setup mode).actor? event).isSome = true)
      (activated : (execution.application.activatedAt event).isSome = true) :
      EventGraphRuntime.State.refreshActivated config execution.application.clock
        execution.application.activatedAt event = execution.application.activatedAt event := by
    obtain ⟨entered, entry⟩ := Option.isSome_iff_exists.mp activated
    obtain ⟨owner, owned⟩ := Option.isSome_iff_exists.mp actor
    simp only [EventGraphRuntime.State.refreshActivated, ready, ↓reduceDIte, owned, entry,
      Option.orElse_some]
  have completion (after : EventGraphRuntime.State (serviceGraph setup mode))
      (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
      (accepted : (serviceApplication setup mode deadline leaks).handle execution.application
        message = some after) : Tables after := by
    have call := reactiveHandle_call accepted
    obtain ⟨clockEq, activatedEq⟩ := handle_clock_activated
      (serviceRuntime setup mode deadline) execution.application after _ call
    refine ⟨clockEq.symm ▸ le_refl _, fun event ready actor activated => ?_, fun field => ?_,
      fun _ => activationKept_refresh after activatedEq⟩
    · rw [activatedEq]
      exact refreshed after.config event ready actor activated
    · rcases message with ⟨mid, ⟨packet, evidence, token⟩⟩
      cases packet with
      | malformed raw => simp [handle] at call
      | opening event candidate raw =>
          exact Or.inl (congrFun (handle_resolution_tables (serviceRuntime setup mode deadline)
            execution.application after _ (fun _ _ impossible => by cases impossible) call).1
            field)
      | commitment event candidate =>
          have tables := (handle_commitment_tables (serviceRuntime setup mode deadline)
            execution.application after mid event candidate call).2.1
          have conditions := handle_publicConditions execution.application after mid
            (.commitment event candidate) call
          obtain ⟨stepped, eventNamed, ready, _⟩ := handle_config_mem_step
            (serviceRuntime setup mode deadline) execution.application after _ call
          have sameEvent : stepped = event := (Option.some.inj eventNamed).symm
          subst stepped
          by_cases same : field = .inr event
          · subst field
            refine Or.inr ⟨?_, event, rfl, ready⟩
            obtain ⟨_, rest⟩ := conditions
            cases view : nodeView (serviceGraph setup mode) event with
            | bind owner payload outputEq codeEq =>
                simp only [view] at rest
                exact rest.2.1
            | resolve _ _ _ _ _ _ => simp only [view] at rest
            | sample _ _ _ _ => simp only [view] at rest
          · exact Or.inl (by rw [tables, Function.update_of_ne same])
  unfold ReactiveApplication.Execution.environmentStep at reached
  rw [PMF.support_map] at reached
  obtain ⟨updated, supported, rfl⟩ := reached
  change Tables updated.application
  cases command with
  | activate who =>
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact unchanged
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact unchanged
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact unchanged
      | some message =>
          change Tables (((serviceApplication setup mode deadline leaks).handle
            execution.application message).getD execution.application)
          cases accepted : (serviceApplication setup mode deadline leaks).handle
              execution.application message with
          | none => exact unchanged
          | some after => exact completion after message accepted
  | application command =>
      rw [PMF.support_map] at supported
      obtain ⟨state, member, rfl⟩ := supported
      replace member : state ∈ (EventGraphRuntime.environmentStep
        (serviceRuntime setup mode deadline)
        (execution.application : EventGraphRuntime.State (serviceGraph setup mode))
          command).support := member
      change Tables state
      have acceptedEq := (environmentStep_tables (serviceRuntime setup mode deadline)
        execution.application state command member).1
      refine ⟨?_, ?_, fun field => Or.inl (by rw [acceptedEq]), ?_⟩
      · cases command with
        | advanceClock =>
            simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
            subst state
            exact Nat.le_succ _
        | executeSample event =>
            exact (environmentStep_executeSample_config_activated
              (serviceRuntime setup mode deadline) execution.application state event
              member).1.symm ▸ le_refl _
        | expire event =>
            exact (environmentStep_expire_config_activated (serviceRuntime setup mode deadline)
              execution.application state event member).1.symm ▸ le_refl _
      · intro event ready actor activated
        cases command with
        | advanceClock =>
            simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
            subst state
            rfl
        | executeSample sampled =>
            rcases (environmentStep_executeSample_config_activated
              (serviceRuntime setup mode deadline) execution.application state sampled
              member).2 with ⟨_, activatedEq⟩ | ⟨_, _, _, activatedEq⟩
            · rw [activatedEq]
            · rw [activatedEq]
              exact refreshed state.config event ready actor activated
        | expire expired =>
            rcases (environmentStep_expire_config_activated (serviceRuntime setup mode deadline)
              execution.application state expired member).2 with
              ⟨_, activatedEq⟩ | ⟨_, _, _, activatedEq⟩
            · rw [activatedEq]
            · rw [activatedEq]
              exact refreshed state.config event ready actor activated
      · intro kept
        cases command with
        | advanceClock =>
            simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
            subst state
            exact kept
        | executeSample sampled =>
            rcases (environmentStep_executeSample_config_activated
              (serviceRuntime setup mode deadline) execution.application state sampled
              member).2 with ⟨configEq, activatedEq⟩ | ⟨_, _, _, activatedEq⟩
            · intro event ready actor
              rw [activatedEq]
              exact kept event (configEq ▸ ready) actor
            · exact activationKept_refresh state activatedEq
        | expire expired =>
            rcases (environmentStep_expire_config_activated (serviceRuntime setup mode deadline)
              execution.application state expired member).2 with
              ⟨configEq, activatedEq⟩ | ⟨_, _, _, activatedEq⟩
            · intro event ready actor
              rw [activatedEq]
              exact kept event (configEq ▸ ready) actor
            · exact activationKept_refresh state activatedEq

/-- The handler's conditions on a call for a ready, activated actor event do
not appear from nothing across one scheduler command that keeps the event
ready. -/
theorem publicConditions_of_environment
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
    (reached : next ∈ (execution.environmentStep
        (serviceApplication setup mode deadline leaks) command).support)
    (call : Payload (serviceGraph setup mode)) (event : (serviceGraph setup mode).EventId)
    (named : call.event? (serviceGraph setup mode) = some event)
    (ready : execution.application.config.cut.Ready event)
    (stillReady : next.application.config.cut.Ready event)
    (actor : ((serviceGraph setup mode).actor? event).isSome = true)
    (activated : (execution.application.activatedAt event).isSome = true)
    (holds : PublicConditions setup deadline next.application call) :
    PublicConditions setup deadline execution.application call := by
  obtain ⟨clockLe, activatedEq, acceptedExtends, _⟩ := environmentStep_handlerTables reached
  have sameActivation := activatedEq event stillReady actor activated
  have timely : next.application.WithinDeadline (serviceRuntime setup mode deadline) event →
      execution.application.WithinDeadline (serviceRuntime setup mode deadline) event := by
    intro within
    unfold EventGraphRuntime.State.WithinDeadline at within ⊢
    rw [sameActivation] at within
    cases entry : execution.application.activatedAt event with
    | none =>
        rw [entry] at within
        exact within
    | some entered =>
        rw [entry] at within
        exact lt_of_le_of_lt (Nat.sub_le_sub_right clockLe entered) within
  cases call with
  | malformed raw => trivial
  | commitment actual candidate =>
      have sameEvent : actual = event := Option.some.inj named
      subst sameEvent
      obtain ⟨within, rest⟩ := holds
      refine ⟨timely within, ?_⟩
      cases view : nodeView (serviceGraph setup mode) actual with
      | bind owner payload outputEq codeEq =>
          simp only [view] at rest ⊢
          obtain ⟨handleOwner, vacant, unused⟩ := rest
          refine ⟨handleOwner, ?_, fun field => ?_⟩
          · rcases acceptedExtends (.inr actual) with same | ⟨empty, _⟩
            · rw [← same]
              exact vacant
            · exact empty
          · rcases acceptedExtends field with same | ⟨empty, _⟩
            · rw [← same]
              exact unused field
            · rw [empty]
              exact fun impossible => by cases impossible
      | resolve _ _ _ _ _ _ => simp only [view] at rest
      | sample _ _ _ _ => simp only [view] at rest
  | opening actual candidate raw =>
      have sameEvent : actual = event := Option.some.inj named
      subst sameEvent
      obtain ⟨within, rest⟩ := holds
      refine ⟨timely within, ?_⟩
      cases view : nodeView (serviceGraph setup mode) actual with
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [view] at rest ⊢
          obtain ⟨handleOwner, associated, typed⟩ := rest
          refine ⟨handleOwner, ?_, typed⟩
          rcases acceptedExtends binding.field with same | ⟨_, other, fieldEq, otherReady⟩
          · rw [← same]
            exact associated
          · exfalso
            have readsEq : ((serviceGraph setup mode).nodes actual).readFields =
                insert binding.field (GuardCheck.listReadFields checks) := by
              calc
                ((serviceGraph setup mode).nodes actual).readFields =
                    (cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
                      ((serviceGraph setup mode).nodes actual)).readFields :=
                  (EventCode.readFields_cast outputEq _).symm
                _ = (EventCode.resolve owner payload binding checks).readFields :=
                  congrArg EventCode.readFields codeEq
                _ = insert binding.field (GuardCheck.listReadFields checks) := rfl
            have present := execution.application.config.read_available ready
              (field := binding.field) (by rw [readsEq]; exact Finset.mem_insert_self _ _)
            rw [fieldEq] at present
            exact otherReady.1 ((execution.application.config.output_available other).mp present)
      | bind _ _ _ _ => simp only [view] at rest
      | sample _ _ _ _ => simp only [view] at rest

/-- A condemned emitted packet stays condemned across a scheduler command. -/
theorem Condemned.environment {execution next :
    (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
        (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep
        (serviceApplication setup mode deadline leaks) command).support)
    (activation : ActivationKept execution.application)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message)
    (marked : Condemned setup leaks execution message) :
    Condemned setup leaks next message := by
  obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
  have step := contractStep_environment
      (serviceRuntime setup mode deadline) leaks execution next command reached
  have prefixOf :=
      (serviceApplication setup mode deadline leaks).environmentStep_receipts_prefix execution next
    command reached
  have emittedEq : ∀ message, Emitted setup leaks execution message →
      Emitted setup leaks next message := by
    intro message emitted
    unfold Emitted at emitted ⊢
    rw [inputsEq]
    exact emitted
  by_cases forbidden : ContentForbidden setup message
  · exact Or.inl forbidden
  rcases marked with forbidden' | ⟨event, named, unaccepted, state⟩ |
      ⟨accepted, event, named, completed, content⟩
  · exact Or.inl forbidden'
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
          (serviceRuntime setup mode deadline) execution.application after _
              (reactiveHandle_call handled)
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
        · by_cases same : other = event
          · subst other
            refine Or.inl ?_
            rw [execution.application.config.step_cut _ otherReady action
              next.application.config member]
            exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
          · have nextReady : next.application.config.cut.Ready event := by
              rw [execution.application.config.step_cut other otherReady action
                next.application.config member]
              exact ready.after_complete otherReady (Ne.symm same)
            refine Or.inr ⟨nextReady, Or.inl fun holds => blocked ?_⟩
            have actor := publicConditions_actor next.application message.payload.call event
              named holds
            exact publicConditions_of_environment reached message.payload.call event named
              ready nextReady actor (activation event ready actor) holds
      · rcases step with ⟨configEq, _, _, _⟩ | ⟨other, otherReady, action, member⟩
        · refine Or.inr ⟨configEq ▸ ready, Or.inr ?_⟩
          have observationEq : next.application.publicView.observation =
              execution.application.publicView.observation := by
            change (serviceGraph setup mode).publicObserve next.application.config =
              (serviceGraph setup mode).publicObserve execution.application.config
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
          | malformed raw => simp only [call] at fails
        · by_cases same : other = event
          · subst other
            refine Or.inl ?_
            rw [execution.application.config.step_cut _ otherReady action
              next.application.config member]
            exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
          have owned : (serviceGraph setup mode).actor? event = some message.sender := by
            by_contra foreign
            exact forbidden (Or.inr (Or.inr (Or.inr (Or.inr ⟨event, named, foreign⟩))))
          have nextReady : next.application.config.cut.Ready event := by
            rw [execution.application.config.step_cut other otherReady action
              next.application.config member]
            exact ready.after_complete otherReady (Ne.symm same)
          refine Or.inr ⟨nextReady, Or.inr ?_⟩
          have extended : next.application.publicView.observation.completionOrder =
              execution.application.publicView.observation.completionOrder ++ [other] := by
            change next.application.config.history.map Completion.event =
              execution.application.config.history.map Completion.event ++ [other]
            rw [execution.application.config.step_history other otherReady action
              next.application.config member]
            simp
          unfold ContentFails at fails ⊢
          cases call : message.payload.call with
          | commitment actual candidate =>
              simp only [call] at fails ⊢
              have foreignBinding : bindingOwnedBy (serviceGraph setup mode) message.sender other =
                  false := by
                unfold bindingOwnedBy
                cases layout : (serviceGraph setup mode).outputLayout other with
                | binding owner payload =>
                    apply decide_eq_false
                    rintro rfl
                    exact same ((serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
                      execution.application.config.cut ready otherReady owned
                      (EventGraph.actor?_of_outputLayout_binding _ layout))
                | publicData _ | privateInput _ _ | publication _ => rfl
              rw [PublicView.bindingCount_eq_countP, extended, List.countP_append,
                ← PublicView.bindingCount_eq_countP]
              simpa [foreignBinding] using fails
          | opening actual candidate raw =>
              simp only [call] at fails ⊢
              rw [State.openingGuardsAccepted_congr execution.application next.application
                message.payload event named (fun predecessor inside => ready.2 inside)
                (fun field value stored => execution.application.config.step_store_of_some
                  next.application.config other otherReady action member field value stored)]
              exact fails
          | malformed raw => simp only [call] at fails
  · refine Or.inr (Or.inr ⟨prefixOf.subset accepted, event, named,
      step.completed_mono completed, fun later => content ?_⟩)
    exact settledContent_of_step step execution.receipts next.receipts message event named
      completed later

/-- Marks survive a scheduler command. -/
theorem Doomed.environment {execution next :
    (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
        (facts : SettledFacts setup leaks execution)
    (reached : next ∈ (execution.environmentStep
        (serviceApplication setup mode deadline leaks) command).support)
    (activation : ActivationKept execution.application)
    {owner : Player} (doomed : Doomed setup leaks execution owner) :
    Doomed setup leaks next owner := by
  obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
  have step := contractStep_environment
      (serviceRuntime setup mode deadline) leaks execution next command reached
  have prefixOf :=
      (serviceApplication setup mode deadline leaks).environmentStep_receipts_prefix execution next
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
      Or.inl (marked.environment facts reached activation emitted)⟩
  · exact ⟨message, emittedEq message emitted, authored,
      Or.inr ⟨other, emittedEq other otherEmitted, otherAuthored, different, event, named,
        otherNamed⟩⟩

/-- An accepted emitted envelope carries a valid token and is sent by its
event's actor. -/
theorem SettledFacts.accepted_emitted {execution :
    (serviceApplication setup mode deadline leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message)
    (accepted : (message.id, true) ∈ execution.receipts) :
    message ∈ execution.network.ledger ∧ message.payload.tokenValid = true ∧
      ∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
        (serviceGraph setup mode).actor? event = some message.sender := by
  obtain ⟨witness, member, identified, valid, event, named, _, owned⟩ :=
    facts.accepted message.id accepted
  have same := facts.emitted_unique (facts.carried.ledger witness member) emitted identified
  subst same
  exact ⟨member, valid, event, named, owned⟩

/-- At a settlement that completed every event, a condemned emitted packet is
forbidden by the settled record. -/
theorem Condemned.forbidden {execution : (serviceApplication setup mode deadline leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    (terminal : execution.application.config.cut.Terminal)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message)
    (marked : Condemned setup leaks execution message) :
    ((serviceRuntime setup mode deadline).settledRecord leaks execution).permits message =
        false := by
  have settledAll : ∀ event, event ∈ ((serviceRuntime setup mode deadline).settledRecord leaks
      execution).view.observation.completionOrder := by
    intro event
    apply (execution.application.config.history_exact event).mpr
    rw [terminal]
    exact Finset.mem_univ event
  have unaccepted : ∀ message event, message.payload.call.event? (serviceGraph setup mode) =
      some event →
      (message.id, true) ∉ execution.receipts →
      ((serviceRuntime setup mode deadline).settledRecord leaks execution).permits message =
          false := by
    intro message event named rejected
    exact SettledRecord.permits_eq_false_of_settled _ message event named (settledAll event)
      fun accepted => rejected accepted.1
  have misformed : ∀ message event, message.payload.call.event? (serviceGraph setup mode) =
      some event →
      ¬ ((serviceRuntime setup mode deadline).settledRecord leaks execution).SettledContent
          message →
      ((serviceRuntime setup mode deadline).settledRecord leaks execution).permits message =
          false := by
    intro message event named rejected
    exact SettledRecord.permits_eq_false_of_settled _ message event named (settledAll event)
      fun accepted => rejected accepted.2
  rcases marked with forbidden | ⟨event, named, rejected, _⟩ |
      ⟨_, event, named, _, content⟩
  · cases call : message.payload.call.event? (serviceGraph setup mode) with
    | none => exact SettledRecord.permits_eq_false_of_none _ message call
    | some event =>
        by_cases accepted : (message.id, true) ∈ execution.receipts
        · obtain ⟨_, valid, acceptedEvent, acceptedNamed, owned⟩ :=
            facts.accepted_emitted emitted accepted
          rw [call] at acceptedNamed
          cases Option.some.inj acceptedNamed
          apply misformed message event call
          rcases forbidden with invalid | unnamed |
              ⟨actual, candidate, committed, evidence⟩ |
              ⟨actual, candidate, raw, opened, uncertified⟩ |
              ⟨foreignEvent, foreignNamed, foreign⟩
          · rw [valid] at invalid
            cases invalid
          · rw [call] at unnamed
            cases unnamed
          · unfold SettledRecord.SettledContent
            rw [committed]
            exact fun content => evidence content.1
          · unfold SettledRecord.SettledContent
            rw [opened]
            intro content
            rw [uncertified] at content
            cases content.1
          · rw [call] at foreignNamed
            cases Option.some.inj foreignNamed
            exact (foreign owned).elim
        · exact unaccepted message event call accepted
  · exact unaccepted message event named rejected
  · exact misformed message event named content

/-- At a settlement that completed every event, a doomed author has an emitted
packet the settled record forbids. -/
theorem Doomed.forbidden {execution : (serviceApplication setup mode deadline leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    (terminal : execution.application.config.cut.Terminal) {who : Player}
    (doomed : Doomed setup leaks execution who) :
    ∃ message, Emitted setup leaks execution message ∧ message.sender = who ∧
      ((serviceRuntime setup mode deadline).settledRecord leaks execution).permits message =
          false := by
  have settledAll : ∀ event, event ∈ ((serviceRuntime setup mode deadline).settledRecord leaks
      execution).view.observation.completionOrder := by
    intro event
    apply (execution.application.config.history_exact event).mpr
    rw [terminal]
    exact Finset.mem_univ event
  have unaccepted : ∀ message event, message.payload.call.event? (serviceGraph setup mode) =
      some event →
      (message.id, true) ∉ execution.receipts →
      ((serviceRuntime setup mode deadline).settledRecord leaks execution).permits message =
          false := by
    intro message event named rejected
    exact SettledRecord.permits_eq_false_of_settled _ message event named (settledAll event)
      fun accepted => rejected accepted.1
  have misformed : ∀ message event, message.payload.call.event? (serviceGraph setup mode) =
      some event →
      ¬ ((serviceRuntime setup mode deadline).settledRecord leaks execution).SettledContent
          message →
      ((serviceRuntime setup mode deadline).settledRecord leaks execution).permits message =
          false := by
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
def BreachesDoomed : (serviceApplication setup mode deadline leaks).ProtocolState → Prop
  | none => True
  | some control => ActivationKept control.execution.application ∧ ∀ record ∈
      (serviceApplication setup mode deadline leaks).executionTraffic control.execution,
      (serviceRuntime setup mode deadline).permittedServiceEnvelope record.observation record.ledger
        record.envelope = false →
      Doomed setup leaks control.execution record.envelope.sender

/-- Every send-time breach in the traffic of a legal history dooms its author,
for every scheduler and arbitrary responses. -/
theorem breachesDoomed_history (initial : PMF
    (serviceApplication setup mode deadline leaks).State) (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (initialKept : ∀ state ∈ initial.support, ActivationKept state) :
    ∀ {state} (_ :
        ((serviceApplication setup mode deadline leaks).protocol initial horizon scheduler).Trace
            state),
      BreachesDoomed state
  | _, .start => trivial
  | _, .extend (source := before) prior joint _ reached => by
      let app := serviceApplication setup mode deadline leaks
      have valid := breachesDoomed_history initial horizon scheduler initialKept prior
      cases before with
      | none =>
          obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
          refine ⟨initialKept state supported, fun record member => ?_⟩
          simp [ReactiveApplication.executionTraffic, ReactiveApplication.Execution.initial,
            ReactiveApplication.trafficViews] at member
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          have facts := settledFacts_history initial horizon scheduler prior
          obtain ⟨kept, doomed⟩ := valid
          cases actor with
          | some who =>
              have traffic := app.stateTraffic_transition initial horizon scheduler
                ⟨_, prior⟩ joint _ reached
              cases (PMF.mem_support_pure_iff _ _).mp reached
              refine ⟨activationKept_respond execution who _ kept, fun record member breach => ?_⟩
              change record ∈ app.stateTraffic (some _) at member
              rw [traffic] at member
              rcases List.mem_append.mp member with prior' | fresh
              · exact (doomed record prior' breach).respond who _
              · simp only [ReactiveApplication.trafficStep, List.mem_map] at fresh
                obtain ⟨input, inside, rfl⟩ := fresh
                refine doomed_of_breach execution facts who _ input ?_ breach
                exact List.mem_of_mem_drop inside
          | none =>
              cases remaining with
              | zero =>
                  cases (PMF.mem_support_pure_iff _ _).mp reached
                  exact ⟨kept, doomed⟩
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  refine ⟨(environmentStep_handlerTables supported).2.2.2 kept,
                    fun record member breach => ?_⟩
                  have recordsEq := app.executionTraffic_environment execution next command
                    supported
                  change record ∈ app.executionTraffic next at member
                  rw [recordsEq] at member
                  exact (doomed record member breach).environment facts supported kept

/-- **Send-time breaches are settled-record breaches.** At every legal history
whose contract completed every event, under arbitrary responses and
scheduling, the author of a transmission that breaks the send-time conformance
rule is also the signed author of a transmission the settled record forbids. -/
theorem settled_breach_of_sendTime_breach (initial : PMF
    (serviceApplication setup mode deadline leaks).State)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (initialKept : ∀ state ∈ initial.support, ActivationKept state)
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol initial horizon scheduler).Trace
      (some control))
    (terminal : control.execution.application.config.cut.Terminal)
    (record : (serviceApplication setup mode deadline leaks).TrafficRecord)
    (present : record ∈
        (serviceApplication setup mode deadline leaks).executionTraffic control.execution)
    (breach :
        (serviceRuntime setup mode deadline).permittedServiceEnvelope record.observation
            record.ledger
      record.envelope = false) :
    ∃ other ∈ (serviceApplication setup mode deadline leaks).executionTraffic control.execution,
      other.envelope.sender = record.envelope.sender ∧
      ((serviceRuntime setup mode deadline).settledRecord leaks control.execution).permits
          other.envelope =
        false := by
  have facts := settledFacts_history initial horizon scheduler trace
  obtain ⟨message, emitted, authored, forbidden⟩ := ((breachesDoomed_history initial horizon
    scheduler initialKept trace).2 record present breach).forbidden facts terminal
  have inputs :=
      (serviceApplication setup mode deadline leaks).stateTraffic_inputs initial horizon scheduler
          trace
  have inputMember : message ∈ control.execution.network.inputs := emitted
  change ((serviceApplication setup mode deadline leaks).executionTraffic control.execution).map
    ReactiveApplication.TrafficRecord.envelope = control.execution.network.inputs at inputs
  rw [← inputs] at inputMember
  obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp inputMember
  exact ⟨other, otherMember, authored, forbidden⟩

/-- **An unacceptable fresh packet is condemned.** A response that submits a
packet which the handler rejects at the state it is emitted in, or an opening
without its exact certificate, condemns that packet, in a graph without binding
events. Evidence soundness and binding provenance hold at every legal
history. -/
theorem condemned_of_unacceptable (execution :
    (serviceApplication setup mode deadline leaks).Execution)
    (facts : SettledFacts setup leaks execution)
    (sound : ((serviceRuntime setup mode deadline).packetEvidence leaks).Sound execution)
    (binding : execution.application.BindingInvariant)
    (publications : ∀ event owner payload,
      (serviceGraph setup mode).outputLayout event ≠ .binding owner payload)
    (who : Player) (material : (serviceApplication setup mode deadline leaks).Submission)
    (departure :
      let state :=
          (serviceApplication setup mode deadline leaks).submit execution.application who material
      let packet := (serviceApplication setup mode deadline leaks).packet state who
          (execution.network.known who)
        material
      (serviceApplication setup mode deadline leaks).handle state
          ⟨(who, execution.network.nextSerial who), packet⟩ = none ∨
        certifiedOpening packet = false) :
    Condemned setup leaks (execution.respond (serviceApplication setup mode deadline leaks) who
      ⟨some material⟩)
      ⟨(who, execution.network.nextSerial who),
        (serviceApplication setup mode deadline leaks).packet
            ((serviceApplication setup mode deadline leaks).submit
          execution.application who material) who (execution.network.known who) material⟩ := by
  let app := serviceApplication setup mode deadline leaks
  let next := execution.respond app who ⟨some material⟩
  let message : Message Player (WitnessedPacket (serviceGraph setup mode)) :=
    ⟨(who, execution.network.nextSerial who),
      app.packet (app.submit execution.application who material) who
        (execution.network.known who) material⟩
  have after := settledFacts_respond execution facts who ⟨some material⟩
  have soundNext :=
      ((serviceRuntime setup mode deadline).packetEvidence leaks).sound_respond execution who
    ⟨some material⟩ sound
  have bindingNext : next.application.BindingInvariant :=
    ((serviceRuntime setup mode deadline).reactiveBindingInvariant leaks).respond execution who _
        binding
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
  by_cases conditions : PublicConditions setup deadline next.application message.payload.call
  swap
  · exact Or.inr (Or.inl ⟨event, named, unaccepted, Or.inr ⟨ready, Or.inl conditions⟩⟩)
  by_cases fails : ContentFails setup next.application message
  · exact Or.inr (Or.inl ⟨event, named, unaccepted, Or.inr ⟨ready, Or.inr fails⟩⟩)
  exfalso
  have fresh := fresh_of_conditions next.application message event named forbidden ready
    conditions fails
  have timely : next.application.WithinDeadline (serviceRuntime setup mode deadline) event := by
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
    | malformed raw => cases named
  rcases departure with rejected | uncertified
  · obtain ⟨accepted, handled⟩ :=
      (serviceRuntime setup mode deadline).freshServiceAcceptable_accepted
      next.application next.application.publicView message
      (EventGraphRuntime.freshServiceEnvelope.acceptable
          (serviceRuntime setup mode deadline) fresh) rfl rfl event
      named timely (fun fact member => soundNext.pending message pendingNext fact member)
      bindingNext
    have reactive : app.handle next.application message = some accepted := by
      rw [reactiveApplication_handle_of_tokenValid
          (serviceRuntime setup mode deadline) leaks _ _ valid]
      exact handled
    change app.handle next.application message = none at rejected
    rw [rejected] at reactive
    cases reactive
  · change certifiedOpening message.payload = false at uncertified
    rcases message with ⟨id, ⟨call, evidence, token⟩⟩
    cases call with
    | opening actual candidate raw =>
        exact forbidden (Or.inr (Or.inr (Or.inr (Or.inl ⟨actual, candidate, raw, rfl,
          uncertified⟩))))
    | commitment actual candidate =>
        change some actual = some event at named
        cases Option.some.inj named
        obtain ⟨_, rest⟩ := conditions
        cases node : nodeView (serviceGraph setup mode) event with
        | bind owner payload outputEq codeEq =>
            exact publications event owner payload outputEq
        | resolve _ _ _ _ _ _ => simp only [node] at rest
        | sample _ _ _ _ => simp only [node] at rest
    | malformed raw => cases named

variable (setup leaks) in
/-- A packet stays condemned along with the settled facts. -/
def CondemnedFacts (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  SettledFacts setup leaks execution ∧ Emitted setup leaks execution message ∧
    Condemned setup leaks execution message ∧ ActivationKept execution.application

/-- Condemnation persists under every response and scheduler command. -/
theorem condemnedFacts_persistent (message : Message Player (WitnessedPacket
    (serviceGraph setup mode)))
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) :
    (serviceApplication setup mode deadline leaks).PolicyInvariant players
        (CondemnedFacts setup leaks message) where
  respond execution who action held _ :=
    ⟨settledFacts_respond execution held.1 who action,
      respond_emitted_mono execution who action held.2.1, held.2.2.1.respond who action,
      activationKept_respond execution who action held.2.2.2⟩
  environment execution next command held reached := by
    obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
    refine ⟨settledFacts_environment execution next command held.1 reached, ?_,
      held.2.2.1.environment held.1 reached held.2.2.2 held.2.1,
      (environmentStep_handlerTables reached).2.2.2 held.2.2.2⟩
    unfold Emitted
    rw [inputsEq]
    exact held.2.1

end Marks

end Vegas
