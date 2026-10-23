/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketActorRecord

/-! # Silence of other players in forced states of an observer

At a history of the one-packet game in a forced state of an observer `who`,
while an event is ready, a player other than `who` keeps silence when it is not
the event's actor, and also when it has already emitted a packet for the event
(`Vegas.onePacket_silent_of_forcedObserver`). A packet for a later event has no
readiness token; a packet for a completed event is a second packet for it,
since that event was completed by an accepted packet of its actor, who
otherwise would owe a failure, which the observer's forced state rules out; and
a packet for the ready event is a second packet once one was emitted. For the
same reasons a transmission of a player other than `who` names the ready event,
of which that player is the actor (`Vegas.onePacket_named_of_forcedObserver`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))

/-- **Silence of other players.** At a history of the one-packet game in a
forced state of `who`, while an event is ready, every one-packet response of a
player other than `who` keeps silence, if that player is not the event's actor
or has already emitted a packet naming the event. -/
theorem onePacket_silent_of_forcedObserver (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (who : Player)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (forced : ForcedState setup leaks who (some control))
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    (other : Player) (notWho : other ≠ who)
    (emitted : (graph setup).actor? event = some other →
      ∃ message ∈ (application setup leaks).outputs (control.execution.recall other),
        message.payload.call.event? (graph setup) = some event)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks other
      (control.execution.recall other)
      (control.execution.observe (application setup leaks) other)) :
    response.transmission = none := by
  let app := application setup leaks
  rcases ((bounds.mem_onePacketActions (runtime setup) leaks other _ _ response).mp member).2 with
    silent | ⟨material, _, permitted⟩
  · exact silent
  exfalso
  have rawTrace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler trace
  obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := forced
  obtain ⟨inputRecall, serialRecall, _⟩ := (runtime setup).countRecall_history leaks rawTrace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler rawTrace
  obtain ⟨recordRank, ⟨residual⟩, record⟩ :=
    actorRecord_history (failureProfile setup.program) horizon scheduler rawTrace
  have sameRank := isPrefix_unique ordered residual.checkpoint.ordered
  subst sameRank
  set envelope := (runtime setup).localEnvelope leaks other (control.execution.recall other)
    (control.execution.observe app other) material with envelopeEq
  obtain ⟨tokenValid, correct, first⟩ := (countPermits_eq_true_iff _ _).mp permitted
  obtain ⟨named, namedEvent, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp tokenValid
  have sender : envelope.sender = other := rfl
  have actor := countCallCorrect_actor _ envelope correct namedEvent
  rw [sender] at actor
  have earlierFirst : ∀ message ∈ control.execution.network.inputs, message.sender = other →
      message.payload.call.event? (graph setup) = some named → False := by
    intro message present messageSender messageNamed
    have recalled : message ∈ app.outputs (control.execution.recall other) := by
      rw [← inputRecall other]
      exact List.mem_filter.mpr ⟨present, by simp [messageSender]⟩
    have lower : message.id.2 < envelope.id.2 := by
      have bound := facts.serials.inputs message present
      change message.id.2 < control.execution.network.nextSerial message.sender at bound
      rw [messageSender, serialRecall other] at bound
      exact bound
    exact first message ⟨recalled, messageSender.trans sender.symm, lower⟩
      (messageNamed.trans namedEvent.symm)
  have issued : ∀ predecessor ∈ (graph setup).order.predecessors named,
      predecessor ∈ control.execution.application.config.cut.completed := by
    have token : control.execution.application.publicView.tokenFor envelope.payload.call =
        some ⟨named⟩ := tokenEq
    unfold PublicView.tokenFor at token
    rw [namedEvent, Option.bind_some] at token
    obtain ⟨_, complete⟩ := (PublicView.readinessToken?_eq_some_iff _ named ⟨named⟩).mp token
    intro predecessor member
    exact (control.execution.application.config.history_exact predecessor).mp
      (complete predecessor member)
  by_cases completed : named ∈ control.execution.application.config.cut.completed
  · rcases record named completed other actor with
      ⟨message, onLedger, _, messageNamed, messageSender⟩ | owed
    · exact earlierFirst message (facts.carried.ledger message onLedger) messageSender
        messageNamed
    · exact ((forcedPoint.2 other notWho).2) (owed point decoded)
  · have same := ready_unique (setup := setup) _ ⟨completed, fun predecessor member =>
      issued predecessor member⟩ ready
    subst same
    obtain ⟨message, recalled, messageNamed⟩ := emitted actor
    rw [← inputRecall other] at recalled
    obtain ⟨present, fromOther⟩ := List.mem_filter.mp recalled
    exact earlierFirst message present (by simpa using fromOther) messageNamed

/-- **A transmission of another player names the ready event.** At a history
of the one-packet game in a forced state of `who`, every transmitting
one-packet response of a player other than `who` names a ready event, of which
that player is the actor. -/
theorem onePacket_named_of_forcedObserver (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (who : Player)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (forced : ForcedState setup leaks who (some control))
    (other : Player) (notWho : other ≠ who)
    {material : (application setup leaks).Submission}
    (member : (⟨some material⟩ : (application setup leaks).Action) ∈
      bounds.onePacketActions (runtime setup) leaks other (control.execution.recall other)
        (control.execution.observe (application setup leaks) other)) :
    ∃ event, control.execution.application.config.cut.Ready event ∧
      material.call.packet.event? (graph setup) = some event ∧
      (graph setup).actor? event = some other := by
  let app := application setup leaks
  rcases ((bounds.mem_onePacketActions (runtime setup) leaks other _ _ _).mp member).2 with
    silent | ⟨material', transmitted, permitted⟩
  · cases silent
  cases transmitted
  have rawTrace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler trace
  obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := forced
  obtain ⟨inputRecall, serialRecall, _⟩ := (runtime setup).countRecall_history leaks rawTrace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler rawTrace
  obtain ⟨recordRank, ⟨residual⟩, record⟩ :=
    actorRecord_history (failureProfile setup.program) horizon scheduler rawTrace
  have sameRank := isPrefix_unique ordered residual.checkpoint.ordered
  subst sameRank
  set envelope := (runtime setup).localEnvelope leaks other (control.execution.recall other)
    (control.execution.observe app other) material with envelopeEq
  obtain ⟨tokenValid, correct, first⟩ := (countPermits_eq_true_iff _ _).mp permitted
  obtain ⟨named, namedEvent, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp tokenValid
  have sender : envelope.sender = other := rfl
  have actor := countCallCorrect_actor _ envelope correct namedEvent
  rw [sender] at actor
  have issued : ∀ predecessor ∈ (graph setup).order.predecessors named,
      predecessor ∈ control.execution.application.config.cut.completed := by
    have token : control.execution.application.publicView.tokenFor envelope.payload.call =
        some ⟨named⟩ := tokenEq
    unfold PublicView.tokenFor at token
    rw [namedEvent, Option.bind_some] at token
    obtain ⟨_, complete⟩ := (PublicView.readinessToken?_eq_some_iff _ named ⟨named⟩).mp token
    intro predecessor member
    exact (control.execution.application.config.history_exact predecessor).mp
      (complete predecessor member)
  by_cases completed : named ∈ control.execution.application.config.cut.completed
  · exfalso
    rcases record named completed other actor with
      ⟨message, onLedger, _, messageNamed, messageSender⟩ | owed
    · have present : message ∈ control.execution.network.inputs :=
        facts.carried.ledger message onLedger
      have recalled : message ∈ app.outputs (control.execution.recall other) := by
        rw [← inputRecall other]
        exact List.mem_filter.mpr ⟨present, by simp [messageSender]⟩
      have lower : message.id.2 < envelope.id.2 := by
        have bound := facts.serials.inputs message present
        change message.id.2 < control.execution.network.nextSerial message.sender at bound
        rw [messageSender, serialRecall other] at bound
        exact bound
      exact first message ⟨recalled, messageSender.trans sender.symm, lower⟩
        (messageNamed.trans namedEvent.symm)
    · exact ((forcedPoint.2 other notWho).2) (owed point decoded)
  · exact ⟨named, ⟨completed, fun predecessor member => issued predecessor member⟩, namedEvent,
      actor⟩

end Vegas
