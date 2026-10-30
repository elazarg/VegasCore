/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletion
import Vegas.Game.SourcePrefixPublications

/-! # Completed events with an actor and the silence of other players

**Failing completions owe a failure.** A source action that commits a failed
binding or withholds a disclosure is *failing* (`Vegas.SourceProgram.Failing`).
The decoded action of a binding event completed with failure, or of a
publication event completed with withholding, is failing
(`Vegas.SourceProgram.decodeEventAction_failing_binding`,
`Vegas.SourceProgram.decodeEventAction_failing_publication`). Stepping a decoded
point with a failing action at the event of a player makes that player owe a
failure (`Vegas.SourceProgram.ProtocolState.owesFailure_of_decode_failing`).

**The actor record.** A scheduler command completes an event with an actor
either by including an accepted packet of that actor naming it, or with a
failing decoded action, as at an expiry (`Vegas.actor_completion_cause`). So at
every legal history of the supplied runtime, under arbitrary responses and
every scheduler, every completed event with an actor was completed by an
accepted packet of its actor, or that actor owes a failure at the decoded point
(`Vegas.actorRecord_history`).

**Silence of the others.** Hence, at a history of the one-packet game in a
forced state of an event's actor, while that event is ready, every one-packet
response of another player keeps silence (`Vegas.onePacket_silent_of_pending`):
a packet for a later event has no readiness token, and a packet for one of the
player's own completed events is a second packet for it.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **How an event with an actor completes.** When a scheduler command completes
an event with an actor, either an included packet of that actor naming the
event was accepted, or the decoded action of the completion is failing, as at an
expired binding or reveal. -/
theorem actor_completion_cause (execution next : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup runtime leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor) :
    (∃ message ∈ next.network.ledger, (message.id, true) ∈ next.receipts ∧
        message.payload.call.event? (graph setup) = some event ∧ message.sender = actor) ∨
      Failing (decodeEventAction setup.program event action) := by
  rcases owned_completion_cases (runtime := runtime) execution next command reached ready action
    member acts with
    accepted | ⟨_, _, _, _, _, expired⟩
  · rcases accepted with ⟨accepted⟩
    exact Or.inl ⟨accepted.message, accepted.ledger,
      accepted.receipt, accepted.named,
      accepted.sender⟩
  · exact Or.inr (expiredAction_failing expired)

/-- **The actor record.** The configuration decodes at a prefix, and every
completed event with an actor was completed by an accepted packet of that actor
naming it, or that actor owes a failure at the decoded point. -/
def ActorRecord (profile : BehavioralProfile setup.program)
    (execution : (application setup runtime leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    ∀ event ∈ execution.application.config.cut.completed, ∀ actor,
      (graph setup).actor? event = some actor →
        (∃ message ∈ execution.network.ledger, (message.id, true) ∈ execution.receipts ∧
          message.payload.call.event? (graph setup) = some event ∧ message.sender = actor) ∨
        DecodedHolds (ProtocolState.OwesFailure actor setup.program) rank
          execution.application.config

/-- The actor record holds at every legal history of the supplied runtime, under
arbitrary responses and every scheduler. -/
theorem actorRecord_serviceInvariant (profile : BehavioralProfile setup.program)
    (scheduler : (application setup runtime leaks).Scheduler) :
    (application setup runtime leaks).ServiceInvariant scheduler (ActorRecord (runtime := runtime)
      profile) where
  respond execution who action valid := by
    have configEq := (runtime.reactive_respond_application leaks execution who action).1
    have ledgerEq := (application setup runtime leaks).respond_ledger execution who action
    have receiptsEq := (application setup runtime leaks).respond_receipts execution who action
    unfold ActorRecord at valid ⊢
    rw [configEq, ledgerEq, receiptsEq]
    exact valid
  environment execution next command valid _ reached := by
    obtain ⟨rank, ⟨residual⟩, record⟩ := valid
    have grows := environment_ledger_receipts_grow (runtime := runtime) execution next command
      reached
    rcases environmentStep_configStep setup leaks execution next command reached with
      same | ⟨event, ready, action, member⟩
    · refine ⟨rank, ?_, fun other completed actor acts => ?_⟩
      · rw [same]
        exact ⟨residual⟩
      · rw [same] at completed ⊢
        rcases record other completed actor acts with
          ⟨message, present, receipt, named, sender⟩ | owed
        · exact Or.inl ⟨message, grows.1 message present, grows.2 _ receipt, named, sender⟩
        · exact Or.inr owed
    · have rankEq : event.val = rank :=
        (ready_iff_rank setup _ rank residual.checkpoint.ordered event).mp ready
      obtain ⟨successor, reachedPoint⟩ := residual.step event ready action _ member
      have advanced : next.application.config.cut.IsPrefix (rank + 1) := by
        rw [execution.application.config.step_cut event ready action _ member]
        exact residual.checkpoint.ordered.complete_at event ready rankEq
      refine ⟨rank + 1, ⟨successor⟩, fun other completed actor acts => ?_⟩
      rw [execution.application.config.step_cut event ready action _ member,
        EventOrder.Cut.mem_complete] at completed
      rcases completed with rfl | earlier
      · rcases actor_completion_cause (runtime := runtime) execution next command reached ready
          action member acts with
          accepted | failing
        · exact Or.inl accepted
        · right
          intro state decoded
          rw [successor.decode] at decoded
          obtain rfl := Option.some.inj decoded
          have decodedBefore := residual.decode
          generalize residual.lift (ProtocolState.entry residual.program residual.source) =
            point at decodedBefore reachedPoint
          rw [← rankEq] at decodedBefore
          have owned : eventOwner? setup.program ⟨other.val, other.isLt⟩ = some actor := by
            rw [eventOwner?_eq_actor]
            exact acts
          exact ProtocolState.owesFailure_of_decode_failing setup.program setup.namesNodup
            other.val _ _ _ _ _ _ point other.isLt actor _ _ decodedBefore owned failing
            reachedPoint
      · rcases record other earlier actor acts with
          ⟨message, present, receipt, named, sender⟩ | owed
        · exact Or.inl ⟨message, grows.1 message present, grows.2 _ receipt, named, sender⟩
        · exact Or.inr (residual.decodedHolds_configStep (fun state joint target owing reached =>
            ProtocolState.owesFailure_step actor setup.program state joint target owing reached)
            owed
            (Or.inr ⟨event, ready, action, member⟩) advanced)

/-- The actor record holds at every legal history of the supplied runtime from
its initial law. -/
theorem actorRecord_history (profile : BehavioralProfile setup.program) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    {control : (application setup runtime leaks).Control}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    ActorRecord (runtime := runtime) profile control.execution :=
  (actorRecord_serviceInvariant (runtime := runtime) profile scheduler).history (initialLaw setup)
    horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      let residual := SourceResidual.initial setup profile initial
      refine ⟨0, ⟨residual⟩, fun event completed => ?_⟩
      have below := (residual.checkpoint.ordered.2 event).mp completed
      exact absurd below (Nat.not_lt_zero _)) trace

/-- The event a permitted call names has its sender as actor. -/
theorem countCallCorrect_actor (earlier : Message Player (WitnessedPacket (graph setup)) → Prop)
    (message : Message Player (WitnessedPacket (graph setup)))
    (correct : CountCallCorrect earlier message) {event : (graph setup).EventId}
    (named : message.payload.call.event? (graph setup) = some event) :
    (graph setup).actor? event = some message.sender := by
  unfold CountCallCorrect at correct
  cases call : message.payload.call with
  | malformed raw =>
      rw [call] at named
      cases named
  | commitment named' handle =>
      rw [call] at named correct
      cases named
      have owned := correct.1
      unfold bindingOwnedBy at owned
      cases view : nodeView (graph setup) event with
      | bind owner payload outputEq codeEq =>
          rw [outputEq] at owned
          have same : owner = message.sender := of_decide_eq_true owned
          rw [← same]
          exact nodeView_bind_actor outputEq codeEq
      | resolve owner payload binding checks outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
      | sample payload law outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
  | opening named' handle raw =>
      rw [call] at named correct
      cases named
      obtain ⟨_, owned⟩ := correct
      cases view : nodeView (graph setup) event with
      | resolve owner payload binding checks outputEq codeEq =>
          rw [view] at owned
          rw [owned.1]
          exact nodeView_resolve_actor outputEq codeEq
      | bind _ _ _ _ =>
          rw [view] at owned
          exact owned.elim
      | sample _ _ _ _ =>
          rw [view] at owned
          exact owned.elim

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **Other players are silent while an event is pending.** At a history of the
one-packet game in a forced state of `owner`, while an event of `owner` is
ready, every one-packet response of another player keeps silence. A packet for
a later event has no readiness token, and a packet for one of the player's own
completed events is a second packet for it: on a forced history its event was
completed by an accepted packet of the player, since otherwise it would owe a
failure. -/
theorem onePacket_silent_of_pending (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler) (owner : Player)
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (forced : ForcedState setup runtime leaks owner history.state)
    {control : (application setup runtime leaks).Control} (current : history.state = some control)
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner) (other : Player) (different : other ≠ owner)
    (response : (application setup runtime leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks other
      (control.execution.recall other)
      (control.execution.observe (application setup runtime leaks) other)) :
    response.transmission = none := by
  let app := application setup runtime leaks
  rcases ((bounds.mem_onePacketActions runtime leaks other _ _ response).mp member).2 with
    silent | ⟨material, _, permitted⟩
  · exact silent
  exfalso
  have trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
    current ▸ (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.trace
  rw [current] at forced
  obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := forced
  obtain ⟨inputRecall, serialRecall, _⟩ := runtime.countRecall_history leaks trace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
  obtain ⟨recordRank, ⟨residual⟩, record⟩ :=
    actorRecord_history (runtime := runtime) (failureProfile setup.program) horizon scheduler trace
  have sameRank := EventOrder.Cut.IsPrefix.unique ordered residual.checkpoint.ordered
  subst sameRank
  set envelope := runtime.localEnvelope leaks other (control.execution.recall other)
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
  have completed : named ∈ control.execution.application.config.cut.completed := by
    by_contra open_
    have same := ready_unique (setup := setup) _ ⟨open_, fun predecessor member =>
      issued predecessor member⟩ ready
    subst same
    exact different (Option.some.inj (actor.symm.trans owned))
  rcases record named completed other actor with
    ⟨message, onLedger, _, messageNamed, messageSender⟩ | owed
  · have emitted : message ∈ control.execution.network.inputs :=
      facts.carried.ledger message onLedger
    have recalled : message ∈ app.outputs (control.execution.recall other) := by
      rw [← inputRecall other]
      exact List.mem_filter.mpr ⟨emitted, by simp [messageSender]⟩
    have lower : message.id.2 < envelope.id.2 := by
      have bound := facts.serials.inputs message emitted
      change message.id.2 < control.execution.network.nextSerial message.sender at bound
      rw [messageSender, serialRecall other] at bound
      exact bound
    exact first message ⟨recalled, messageSender.trans sender.symm, lower⟩
      (messageNamed.trans namedEvent.symm)
  · exact ((forcedPoint.2 other different).2) (owed point decoded)

end Vegas
