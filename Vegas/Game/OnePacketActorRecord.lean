module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketCompletion
public import Vegas.Game.OnePacketForced
public import Vegas.Game.SourceServiceFacts
public import Vegas.Pending.ReactiveOnePacketMenu
public import Interaction.ReactivePublication

@[expose] public section

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
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **How an event with an actor completes.** When a scheduler command completes
an event with an actor, either an included packet of that actor naming the
event was accepted, or the decoded action of the completion is failing, as at an
expired binding or reveal. -/
theorem actor_completion_cause (execution next : (application setup timeouts leaks).Execution)
    (command : (application setup timeouts leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup timeouts leaks)
      command).support)
    (record : (graph setup).Completion) (fresh : record ∉ execution.application.config.history)
    (present : record ∈ next.application.config.history)
    {actor : Player} (acts : (graph setup).actor? record.event = some actor) :
    (∃ message ∈ next.network.ledger, (message.id, true) ∈ next.receipts ∧
        message.payload.call.event? (graph setup) = some record.event ∧ message.sender = actor) ∨
      Failing (record.decision.bind (decodeEventAction setup.program record.event)) := by
  rcases owned_completion_cases (timeouts := timeouts) execution next command reached record fresh
    present acts with accepted | expired | automatic
  · obtain ⟨accepted⟩ := accepted
    exact Or.inl ⟨accepted.message, accepted.ledger, accepted.receipt, accepted.named,
      accepted.sender⟩
  · obtain ⟨_, _, _, _, action, value, expires, recorded⟩ := expired
    have decision := eq_of_heq (EventCompletion.mk.inj recorded).2.1
    rw [decision]
    exact Or.inr (expired_record_failing execution.application.config expires)
  · obtain ⟨_, _, _, _, silent, _, _⟩ := automatic
    right
    simp only [silent, Option.bind_none]
    simp [Failing, OwnAction.disclosure]

/-- **The actor record.** The configuration decodes at a prefix, and every
completed event with an actor was completed by an accepted packet of that actor
naming it, or that actor owes a failure at the decoded point. -/
def ActorRecord (profile : BehavioralProfile setup.program)
    (execution : (application setup timeouts leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    ∀ event ∈ execution.application.config.cut.completed, ∀ actor,
      (graph setup).actor? event = some actor →
        (∃ message ∈ execution.network.ledger, (message.id, true) ∈ execution.receipts ∧
          message.payload.call.event? (graph setup) = some event ∧ message.sender = actor) ∨
        DecodedHolds (ProtocolState.OwesFailure actor setup.program) rank
          execution.application.config

private theorem SourceResidual.debt_of_failing_record_path
    {profile : BehavioralProfile setup.program}
    {before after : (graph setup).Config}
    (path : Relation.ReflTransGen EventGraph.Config.Step before after) :
    ∀ {rank}, SourceResidual setup profile rank before → ∀ record : (graph setup).Completion,
      record ∉ before.history → record ∈ after.history → ∀ {actor},
      (graph setup).actor? record.event = some actor →
      Failing (record.decision.bind (decodeEventAction setup.program record.event)) →
      ∃ nextRank, Nonempty (SourceResidual setup profile nextRank after) ∧
        DecodedHolds (ProtocolState.OwesFailure actor setup.program) nextRank after := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro rank residual record fresh present actor owned failed
      exact (fresh present).elim
  | @head current middle moved rest ih =>
      intro rank residual record fresh present actor owned failed
      obtain ⟨event, ready, action, supported⟩ := moved
      by_cases primary : record ∈ middle.history
      · obtain ⟨value, _output, history⟩ :=
          current.step_completion event ready action middle supported
        rw [history] at primary
        have recorded := List.mem_singleton.mp ((List.mem_append.mp primary).resolve_left fresh)
        have eventEq : record.event = event := congrArg EventCompletion.event recorded
        subst event
        have failingStep : ∃ choice : (graph setup).Action record.event,
            middle ∈ (current.step record.event ready choice).support ∧
              Failing (decodeEventAction setup.program record.event choice) := by
          by_cases inactive : actor ∈ current.defaulted
          · have expires : ∃ choice : (graph setup).Action record.event,
                ExpiredAction record.event choice := by
              cases view : nodeView (graph setup) record.event with
              | bind owner payload outputEq codeEq =>
                  exact ⟨_, .binding owner payload outputEq⟩
              | resolve owner payload binding checks outputEq codeEq =>
                  exact ⟨_, .publication payload outputEq⟩
              | sample payload law outputEq codeEq =>
                  rw [nodeView_sample_actor outputEq codeEq] at owned
                  cases owned
            obtain ⟨choice, expired⟩ := expires
            refine ⟨choice, ?_, expiredAction_failing expired⟩
            rw [← current.step_eq_of_defaulted record.event ready actor owned inactive
              action choice]
            exact supported
          · rw [current.actualDecision_of_active record.event actor owned inactive] at recorded
            have decision := eq_of_heq (EventCompletion.mk.inj recorded).2.1
            exact ⟨action, supported, by
              simpa only [decision, Option.bind_some] using failed⟩
        obtain ⟨choice, supportedChoice, failing⟩ := failingStep
        obtain ⟨next, reachedPoint⟩ :=
          residual.step record.event ready choice middle supportedChoice
        have rankEq : record.event.val = rank := by
          have actual : current.cut.IsPrefix record.event.val :=
            ⟨record.event.isLt.le, fun query =>
              setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
          exact actual.unique residual.checkpoint.ordered
        have debt : DecodedHolds (ProtocolState.OwesFailure actor setup.program)
            (rank + 1) middle := by
          intro source decoded
          rw [next.decode] at decoded
          obtain rfl := Option.some.inj decoded
          have decodedBefore := residual.decode
          generalize residual.lift (ProtocolState.entry residual.program residual.source) =
            point at decodedBefore reachedPoint
          rw [← rankEq] at decodedBefore
          unfold sourceServicePrefix? serviceSourcePrefix? at decodedBefore
          have sourceActor : eventOwner? setup.program record.event = some actor :=
            (eventOwner?_eq_actor setup.program record.event).trans owned
          exact ProtocolState.owesFailure_of_decode_failing setup.program setup.namesNodup
            record.event.val _ _ _ _ _ _ _ point record.event.isLt actor _ _ decodedBefore
            sourceActor failing reachedPoint
        exact next.decodedHolds_path (owesFailure_stepClosed actor) debt rest
      · obtain ⟨next, _reachedPoint⟩ := residual.step event ready action middle supported
        exact ih next record primary present owned failed

/-- The actor record holds at every legal history of the supplied runtime, under
arbitrary responses and every scheduler. -/
theorem actorRecord_serviceInvariant (profile : BehavioralProfile setup.program)
    (scheduler : (application setup timeouts leaks).Scheduler) :
    (application setup timeouts leaks).ServiceInvariant scheduler (ActorRecord (timeouts :=
      timeouts)
      profile) where
  respond execution who action valid := by
    have configEq := ((reactive_respond_application timeouts) leaks execution who action).1
    have ledgerEq := (application setup timeouts leaks).respond_ledger execution who action
    have receiptsEq := (application setup timeouts leaks).respond_receipts execution who action
    unfold ActorRecord at valid ⊢
    rw [configEq, ledgerEq, receiptsEq]
    exact valid
  environment execution next command valid _ reached := by
    let app := application setup timeouts leaks
    obtain ⟨rank, ⟨residual⟩, record⟩ := valid
    have path := ((reactiveApplication_graphSteps timeouts) leaks).environmentStep
      execution next command reached
    obtain ⟨nextRank, ⟨successor⟩⟩ := residual.path path
    have ledger : execution.network.ledger ⊆ next.network.ledger := by
      apply app.environmentStep_cases execution next command reached
        (predicate := fun _ next => execution.network.ledger ⊆ next.network.ledger)
      · exact List.Subset.refl _
      · intros; exact List.Subset.refl _
      · intro id
        change execution.network.ledger ⊆ (execution.includePending app id).network.ledger
        rw [app.includePending_network]
        cases found : execution.network.lookup id with
        | none =>
            simp only [MessageNetwork.includePending, found]
            exact List.Subset.refl _
        | some message =>
            simp only [MessageNetwork.includePending, found]
            exact List.subset_append_left _ _
      · intros; exact List.Subset.refl _
    have receipts := app.environmentStep_receipts_prefix execution next command reached
    refine ⟨nextRank, ⟨successor⟩, fun event completed actor acts => ?_⟩
    by_cases prior : event ∈ execution.application.config.cut.completed
    · rcases record event prior actor acts with accepted | owed
      · obtain ⟨message, present, receipt, named, sender⟩ := accepted
        exact Or.inl ⟨message, ledger present, receipts.subset receipt, named, sender⟩
      · obtain ⟨owedRank, ⟨owedResidual⟩, holds⟩ :=
          residual.decodedHolds_path (owesFailure_stepClosed actor) owed path
        have same := owedResidual.checkpoint.ordered.unique successor.checkpoint.ordered
        exact Or.inr (by simpa only [same] using holds)
    · obtain ⟨completion, present, eventEq⟩ :=
        List.mem_map.mp ((next.application.config.history_exact event).mpr completed)
      have fresh : completion ∉ execution.application.config.history := by
        intro old
        apply prior
        rw [← eventEq]
        exact (execution.application.config.history_exact completion.event).mp
          (List.mem_map_of_mem old)
      have owned : (graph setup).actor? completion.event = some actor := eventEq ▸ acts
      rcases actor_completion_cause execution next command reached completion fresh present owned
        with accepted | failed
      · exact Or.inl (by simpa only [eventEq] using accepted)
      · obtain ⟨owedRank, ⟨owedResidual⟩, holds⟩ :=
          SourceResidual.debt_of_failing_record_path path residual completion fresh present
            owned failed
        have same := owedResidual.checkpoint.ordered.unique successor.checkpoint.ordered
        exact Or.inr (by simpa only [same] using holds)

/-- The actor record holds at every legal history of the supplied runtime from
its initial law. -/
theorem actorRecord_history (profile : BehavioralProfile setup.program) (horizon : Nat)
    (scheduler : (application setup timeouts leaks).Scheduler)
    {control : (application setup timeouts leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control)) :
    ActorRecord (timeouts := timeouts) profile control.execution :=
  (actorRecord_serviceInvariant (timeouts := timeouts) profile scheduler).history (initialLaw setup)
    horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      let residual := SourceResidual.initial setup profile initial
      refine ⟨0, ⟨residual⟩, fun event completed => ?_⟩
      have below := (residual.checkpoint.ordered.2 event).mp completed
      exact absurd below (Nat.not_lt_zero _)) trace


variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **Other players are silent while an event is pending.** At a history of the
one-packet game in a forced state of `owner`, while an event of `owner` is
ready, every one-packet response of another player keeps silence. A packet for
a later event has no readiness token, and a packet for one of the player's own
completed events is a second packet for it: on a forced history its event was
completed by an accepted packet of the player, since otherwise it would owe a
failure. -/
theorem onePacket_silent_of_pending (horizon : Nat)
    (scheduler : (application setup timeouts leaks).Scheduler) (owner : Player)
    (history : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (forced : ForcedState setup timeouts leaks owner history.state)
    {control : (application setup timeouts leaks).Control} (current : history.state = some control)
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner) (other : Player) (different : other ≠ owner)
    (response : (application setup timeouts leaks).Action)
    (member : response ∈ bounds.onePacketActions timeouts leaks other
      (control.execution.logs other)
      (control.execution.observe (application setup timeouts leaks) other)) :
    response.transmission = none := by
  let app := application setup timeouts leaks
  rcases ((bounds.mem_onePacketActions timeouts leaks other _ _ response).mp member).2 with
    silent | ⟨material, _, permitted⟩
  · exact silent
  exfalso
  have trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
    current ▸ (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.trace
  rw [current] at forced
  obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := forced
  obtain ⟨inputRecall, serialRecall, _⟩ := (countRecall_history timeouts) leaks trace
  have facts := legalFacts setup leaks horizon scheduler control trace
  obtain ⟨recordRank, ⟨residual⟩, record⟩ :=
    actorRecord_history (timeouts := timeouts) (failureProfile setup.program) horizon scheduler
      trace
  have sameRank := EventOrder.Cut.IsPrefix.unique ordered residual.checkpoint.ordered
  subst sameRank
  set envelope := (localEnvelope timeouts) leaks other (control.execution.logs other)
    (control.execution.observe app other) material with envelopeEq
  obtain ⟨tokenValid, correct, first⟩ := (countPermits_eq_true_iff _ _).mp permitted
  obtain ⟨named, namedEvent, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp tokenValid
  have sender : envelope.sender = other := rfl
  have actor := correct.actor namedEvent
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
    have same := setup.eventGraph.sequentialize_ready_unique _
      ⟨open_, fun predecessor member => issued predecessor member⟩ ready
    subst same
    exact different (Option.some.inj (actor.symm.trans owned))
  rcases record named completed other actor with
    ⟨message, onLedger, _, messageNamed, messageSender⟩ | owed
  · obtain ⟨entry, entryPresent, material, _transmission, emitted, _packet⟩ :=
      facts.provenance.ledger message onLedger
    have recalled : message ∈ app.outputs (control.execution.logs other) := by
      apply List.mem_filterMap.mpr
      exact ⟨entry, messageSender ▸ entryPresent, emitted⟩
    have emitted : message ∈ control.execution.network.inputs := by
      rw [← inputRecall other] at recalled
      exact (List.mem_filter.mp recalled).1
    have lower : message.id.2 < envelope.id.2 := by
      have bound := facts.serials.inputs message emitted
      change message.id.2 < control.execution.network.nextSerial message.sender at bound
      rw [messageSender, serialRecall other] at bound
      exact bound
    exact first message ⟨recalled, messageSender.trans sender.symm, lower⟩
      (messageNamed.trans namedEvent.symm)
  · exact ((forcedPoint.2 other different).2) (owed point decoded)

end Vegas
