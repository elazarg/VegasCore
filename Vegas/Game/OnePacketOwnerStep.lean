/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLumpingInstance

/-! # The owner's step of the one-packet game at a pending publication

A response changes the operational state only through the envelope it emits:
the actor clears, the envelope joins the network, and the responder's recall
gains its current operational view with the envelope
(`Vegas.operationalState_respond`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The envelope a response emits. -/
def emittedEnvelope (execution : (application setup leaks).Execution) (who : Player)
    (action : (application setup leaks).Action) :
    Option (Message Player (application setup leaks).Payload) :=
  match action.transmission with
  | none => none
  | some submission => some ⟨(who, execution.network.nextSerial who),
      (application setup leaks).packet
        ((application setup leaks).submit execution.application who submission) who
        (execution.network.known who) submission⟩

/-- A response on the operational state: the actor clears, the emitted envelope
joins the network, and the responder's recall gains its current operational
view with the envelope. -/
def OperationalState.respond (responder : Player)
    (emitted : Option (Message Player (application setup leaks).Payload))
    (state : OperationalState setup leaks) : OperationalState setup leaks :=
  { state with
    actor := none
    environment := { state.environment with
      network := match emitted with
        | none => state.environment.network
        | some envelope => (state.network.submit responder envelope.payload).2.publicView }
    keys := fun who => if who = responder then (state.keys who).map fun key =>
      { key with recalled := key.recalled ++ [(key.current, emitted)] } else state.keys who }

/-- A response leaves every player's operational view and delivered value
unchanged. -/
theorem respond_observe_operational (execution : (application setup leaks).Execution)
    (responder : Player) (action : (application setup leaks).Action) (who : Player) :
    operationalView setup leaks ((execution.respond (application setup leaks) responder
        action).observe (application setup leaks) who) =
      operationalView setup leaks (execution.observe (application setup leaks) who) ∧
    deliveredValue setup leaks who ((execution.respond (application setup leaks) responder
        action).observe (application setup leaks) who) =
      deliveredValue setup leaks who (execution.observe (application setup leaks) who) := by
  have contract := (runtime setup).reactive_respond_application leaks execution responder action
  constructor
  · change ((execution.respond (application setup leaks) responder action).application.publicView,
        (execution.respond (application setup leaks) responder action).network.observe who,
        (execution.respond (application setup leaks) responder action).receipts) =
      (execution.application.publicView, execution.network.observe who, execution.receipts)
    rw [contract.2]
    rcases action with ⟨_ | _⟩ <;> rfl
  · apply deliveredValue_congr
    · change (execution.respond (application setup leaks) responder
        action).application.publicView.ownTurn? who = execution.application.publicView.ownTurn? who
      rw [contract.2]
    · change ((graph setup).playerObserve who
          (execution.respond (application setup leaks) responder action).application.config).store =
        ((graph setup).playerObserve who execution.application.config).store
      rw [contract.1]

/-- **A response on the operational state.** -/
theorem operationalState_respond (control : (application setup leaks).Control)
    (responder : Player) (action : (application setup leaks).Action) :
    operationalState setup leaks (some { control with
      actor := none
      execution := control.execution.respond (application setup leaks) responder action }) =
      (operationalState setup leaks (some control)).map
        (OperationalState.respond responder
          (emittedEnvelope control.execution responder action)) := by
  have contract := (runtime setup).reactive_respond_application leaks control.execution
    responder action
  rcases control with ⟨remaining, actor, execution⟩
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [operationalState, Option.map_some, OperationalState.respond, emittedEnvelope,
        Option.some.injEq, OperationalState.mk.injEq]
      refine ⟨trivial, trivial, rfl, rfl, rfl, ?_⟩
      funext who
      by_cases same : who = responder
      · subst same
        simp only [↓reduceIte, Option.map_some, lateKey, ReactiveApplication.Execution.respond,
          List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]
        rw [(application setup leaks).respond_recall_other execution responder who same]
        rfl
  | some submission =>
      simp only [operationalState, Option.map_some, OperationalState.respond, emittedEnvelope,
        Option.some.injEq, OperationalState.mk.injEq]
      refine ⟨trivial, trivial, rfl, ?_, rfl, ?_⟩
      · unfold ReactiveApplication.Execution.observeEnvironment
        congr 1
        exact contract.2
      · funext who
        obtain ⟨current, delivered⟩ := respond_observe_operational execution responder
          ⟨some submission⟩ who
        by_cases same : who = responder
        · subst same
          simp only [↓reduceIte, Option.map_some, lateKey, Option.some.injEq, LateKey.mk.injEq]
          refine ⟨trivial, current, ?_, delivered⟩
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
            List.map_cons, List.map_nil]
          rfl
        · simp only [same, ↓reduceIte, lateKey, Option.some.injEq, LateKey.mk.injEq]
          rw [(application setup leaks).respond_recall_other execution responder who same]
          exact ⟨trivial, current, rfl, delivered⟩

/-- **An opening of a bound value.** The response opens the event with the
handle accepted at the binding, carrying the binding's successful value. -/
def OpensBinding (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (action : (application setup leaks).Action) : Prop :=
  ∃ submission candidate value, action.transmission = some submission ∧
    submission.call.packet = .opening event candidate ⟨payload, value⟩ ∧
    execution.application.accepted binding.field = some candidate ∧
    binding.get? execution.application.config.store = some (.success value)

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **The envelope of a menu opening.** At a state of a one-packet history, a
one-packet response opening an event emits the next envelope of the responder
carrying that opening, its own certificate, and the event's token. -/
theorem emittedEnvelope_of_opening {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    {control : (application setup leaks).Control} (current : history.state = some control)
    (who : Player) (action : (application setup leaks).Action)
    (member : action ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    {submission : (application setup leaks).Submission}
    (sent : action.transmission = some submission)
    {event : (graph setup).EventId} {candidate : Handle (graph setup)} {raw : Raw L}
    (call : submission.call.packet = .opening event candidate raw) :
    emittedEnvelope control.execution who action =
      some ⟨(who, control.execution.network.nextSerial who),
        ⟨.opening event candidate raw, some ⟨candidate, raw⟩, some ⟨event⟩⟩⟩ := by
  rcases ((bounds.mem_onePacketActions (runtime setup) leaks who _ _ action).mp member).2 with
    silent | ⟨material, sentMaterial, permitted⟩
  · rw [sent] at silent
    cases silent
  rw [sent] at sentMaterial
  cases sentMaterial
  have trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    current ▸ (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.trace
  obtain ⟨inputRecall, serialRecall, _⟩ := (runtime setup).countRecall_history leaks trace
  have local_ := (runtime setup).localEnvelope_eq_of_recall leaks control.execution inputRecall
    serialRecall who submission
  obtain ⟨tokenValid, correct, _⟩ := (countPermits_eq_true_iff _ _).mp permitted
  rw [local_] at tokenValid correct
  unfold emittedEnvelope
  rw [sent]
  simp only [Option.some.injEq, Message.mk.injEq, true_and]
  set packet := (application setup leaks).packet ((application setup leaks).submit
    control.execution.application who submission) who (control.execution.network.known who)
    submission with packetEq
  have packetCall : packet.call = .opening event candidate raw := call
  have certified : certifiedOpening packet = true := by
    unfold CountCallCorrect at correct
    simp only [packetCall] at correct
    exact correct.1
  obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ := (WitnessedPacket.tokenValid_iff packet).mp tokenValid
  rw [packetCall] at tokenNamed
  cases tokenNamed
  obtain ⟨shapeEvent, shapeCandidate, shapeRaw, shapeToken, shape⟩ :=
    (certifiedOpening_iff packet).mp certified
  have shapeCall := congrArg WitnessedPacket.call shape
  rw [packetCall] at shapeCall
  cases shapeCall
  rw [shape] at tokenEq ⊢
  cases tokenEq
  rfl

omit [Fintype Player] in
/-- A key decides at most one publication event. -/
theorem turnEvent_of_publicationTurn {key : LateKey setup leaks} {event : (graph setup).EventId}
    (turn : PublicationTurn key event) : turnEvent key = some event := by
  have exists_ : ∃ event, PublicationTurn key event := ⟨event, turn⟩
  unfold turnEvent
  rw [dite_eq_left exists_]
  have chosen := exists_.choose_spec.1
  rw [turn.1] at chosen
  exact congrArg some (Option.some.inj chosen).symm

omit [Fintype Player] in
/-- **The image of a response while the event is pending.** It is the
operational state after the response's emitted envelope. -/
theorem pendingImage_respond {remaining : Nat} {who : Player}
    {execution : (application setup leaks).Execution} {event : (graph setup).EventId}
    (pending : event ∉ execution.application.config.cut.completed)
    (action : (application setup leaks).Action) :
    pendingImage event (some ⟨remaining, none, execution.respond (application setup leaks) who
        action⟩) =
      .inl ((operationalState setup leaks (some ⟨remaining, some who, execution⟩)).map
        (OperationalState.respond who (emittedEnvelope execution who action))) := by
  rw [pendingImage_of_pending _ (by
    change event ∉ (execution.respond (application setup leaks) who
      action).application.config.cut.completed
    rw [((runtime setup).reactive_respond_application leaks execution who action).1]
    exact pending)]
  exact congrArg Sum.inl (operationalState_respond ⟨remaining, some who, execution⟩ who action)

/-- **Openings of the bound value are read off the operational state.** At
states of one-packet histories with the same operational state, while a
publication event is ready, menu openings of its binding's value lead to the
same image. -/
theorem opensBinding_image_congr {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {remaining : Nat} {owner : Player}
    (firstHistory secondHistory : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    {first second : (application setup leaks).Execution}
    (firstCurrent : firstHistory.state = some ⟨remaining, some owner, first⟩)
    (secondCurrent : secondHistory.state = some ⟨remaining, some owner, second⟩)
    (same : operationalState setup leaks (some ⟨remaining, some owner, first⟩) =
      operationalState setup leaks (some ⟨remaining, some owner, second⟩))
    {event : (graph setup).EventId} (ready : first.application.config.cut.Ready event)
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (firstAction secondAction : (application setup leaks).Action)
    (firstMember : firstAction ∈ bounds.onePacketActions (runtime setup) leaks owner
      (first.recall owner) (first.observe (application setup leaks) owner))
    (secondMember : secondAction ∈ bounds.onePacketActions (runtime setup) leaks owner
      (second.recall owner) (second.observe (application setup leaks) owner))
    (firstOpens : OpensBinding first event binding firstAction)
    (secondOpens : OpensBinding second event binding secondAction) :
    pendingImage event (some ⟨remaining, none, first.respond (application setup leaks) owner
        firstAction⟩) =
      pendingImage event (some ⟨remaining, none, second.respond (application setup leaks) owner
        secondAction⟩) := by
  have ready' : second.application.config.cut.Ready event :=
    (SameOperational.ready same event).mp ready
  obtain ⟨firstSubmission, firstCandidate, firstValue, firstSent, firstCall, firstAccepted,
    firstStored⟩ := firstOpens
  obtain ⟨secondSubmission, secondCandidate, secondValue, secondSent, secondCall, secondAccepted,
    secondStored⟩ := secondOpens
  have accepted : first.application.accepted = second.application.accepted :=
    congrArg PublicView.accepted (SameOperational.publicView same)
  rw [accepted, secondAccepted] at firstAccepted
  cases Option.some.inj firstAccepted
  have bindings := SameOperational.binding same ready view
  rw [firstStored, secondStored] at bindings
  cases (PublicationResult.success.inj (Option.some.inj bindings))
  have networks : first.network = second.network := SameOperational.network same
  have emitted : emittedEnvelope first owner firstAction =
      emittedEnvelope second owner secondAction := by
    rw [emittedEnvelope_of_opening bounds firstHistory firstCurrent owner firstAction firstMember
        firstSent firstCall,
      emittedEnvelope_of_opening bounds secondHistory secondCurrent owner secondAction
        secondMember secondSent secondCall, networks]
  rw [pendingImage_respond ready.1, pendingImage_respond ready'.1, same, emitted]

end Vegas
