/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCanonicalPermits
import Vegas.Game.SourceServiceFreshCall
import Vegas.Pending.ReactiveAsyncContract

/-! # Canonical packets sent on time are accepted

At every history of the service runtime, under arbitrary responses and
scheduler choices, the canonical decision of `who` at its turn, while the event
is within its deadline, transmits a packet the contract accepts on the view it
was sent from (`Vegas.canonicalServiceDecision_freshServiceAcceptable`): a
commitment is includable, with a vacant event and a fresh handle that no field
has accepted, and an opening is the certified opening of the accepted handle.
Public guards determine the resulting publication. Sent early enough for an inclusion within
`bound event` slots to land before the deadline, its recall entry is a fresh
call (`Vegas.canonical_freshCall`).

At a history of the one-packet game every own packet is permitted by the count
verdict on the traffic, so no own packet other than a given one names the same
event: of two own packets for one event, the later is forbidden
(`Vegas.onePacket_not_emitsOtherFor`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **A canonical decision sent in time is acceptable.** At every history of
the service runtime, the canonical decision of `who` at its turn `event`,
within the event's deadline, transmits a packet the contract accepts on the
current view. -/
theorem canonicalServiceDecision_freshServiceAcceptable {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (within : control.execution.application.publicView.WithinDeadline
      (serviceRuntime setup mode deadline) event)
    (action : (serviceGraph setup mode).Action event)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (submits : ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) event
      action).transmission = some material) :
    (serviceRuntime setup mode deadline).freshServiceAcceptable
      control.execution.application.publicView
      ⟨(who, control.execution.network.nextSerial who),
        (serviceApplication setup mode deadline leaks).packet
          ((serviceApplication setup mode deadline leaks).submit control.execution.application
            who material) who (control.execution.network.known who) material⟩ := by
  have bindingValid := ((serviceRuntime setup mode deadline).reactiveBindingInvariant leaks).history
    (serviceInitialLaw setup mode) horizon scheduler (fun state member => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
      exact State.initial_bindingInvariant _) trace
  have inputs := (serviceApplication setup mode deadline leaks).history_inputRecall
    (serviceInitialLaw setup mode) horizon scheduler trace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (control.execution.application.publicView_eventReady event).mp readyView
  have activeView := (serviceRuntime setup mode deadline).canonicalServiceDecision_active leaks
    who (control.execution.recall who)
    (control.execution.observe (serviceApplication setup mode deadline leaks) who)
    event action material submits
  have active : who ∉ control.execution.application.config.defaulted := activeView
  have inTime : (match control.execution.application.activatedAt event with
      | none => False
      | some entered => control.execution.application.clock - entered <
          (serviceRuntime setup mode deadline).deadline event) := within
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind actor payload outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨choice, rfl⟩ : ∃ choice : Option (PublicationResult (L.Val payload)),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      cases choice with
      | none =>
          rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_binding_none leaks
            actor _ _ event actor payload outputEq codeEq node] at submits
          cases submits
      | some choice =>
        cases selected : canonicalFreshSlot actor
            (control.execution.observe (serviceApplication setup mode deadline leaks)
              actor).application with
        | none =>
            simp only [EventGraphRuntime.canonicalServiceDecision,
              EventGraphRuntime.canonicalReactiveDecision, ite_eq_right activeView,
              node, cast_cast, cast_eq, Option.bind_some, selected, Option.map_none,
              ReactiveApplication.SubmissionNormalization.action] at submits
            cases submits
        | some serial =>
            have fresh := canonicalFreshSlot_spec actor _ serial selected
            rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_binding leaks actor
              (control.execution.recall actor)
              (control.execution.observe (serviceApplication setup mode deadline leaks) actor) event
              payload outputEq codeEq node activeView serial selected choice] at submits
            cases Option.some.inj submits
            have vacant : control.execution.application.accepted (.inr event) = none := by
              cases associated : control.execution.application.accepted (.inr event) with
              | none => rfl
              | some candidate =>
                  exact False.elim (ready.1
                    (bindingValid.toAssociationInvariant.accepted_complete event candidate
                      associated))
            have unused : ∀ field, control.execution.application.accepted field ≠
                some (actor, .prepared serial) :=
              fun field associated => bindingValid.accepted_fixed field _ associated fresh
            rw [reactiveApplication_packet_none,
              control.execution.application.publicView_tokenFor_of_ready _ event rfl ready]
            refine ⟨?_, rfl⟩
            simp only [PublicView.BindingIncludable, node]
            exact ⟨active, readyView, inTime, by trivial, by trivial, vacant, unused⟩
  | resolve actor payload binding checks outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_eq_of_not_bind leaks actor
        (control.execution.recall actor)
        (control.execution.observe (serviceApplication setup mode deadline leaks) actor) event
        action (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at submits
      unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at submits
      simp only [ite_eq_right activeView, node] at submits
      rcases reactiveResolutionPacket_shape actor event payload binding checks outputEq action
          (control.execution.observe (serviceApplication setup mode deadline leaks)
            actor).application with ⟨candidate, raw, packet⟩ | packet
      · obtain ⟨_, isTrue, _, value, localStored, associated, handleOwner, rawEq⟩ :=
          reactiveResolutionPacket_opening_spec actor event payload binding checks outputEq action
            (control.execution.observe (serviceApplication setup mode deadline leaks)
              actor).application event candidate raw packet
        subst rawEq
        have stored : binding.get? control.execution.application.config.store =
            some (.success value) := by
          change binding.get? ((serviceGraph setup mode).playerStore actor
            control.execution.application.config.store) = _ at localStored
          rwa [binding.get?_playerStore actor control.execution.application.config.store rfl]
            at localStored
        obtain ⟨handle, associatedHandle, _, fixed⟩ :=
          bindingValid.success_provenance binding value stored
        have handleEq : handle = candidate := by
          have same : control.execution.application.accepted binding.field = some candidate :=
            associated
          rw [associatedHandle] at same
          exact Option.some.inj same
        subst handleEq
        have actionEq : action =
            cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
          rw [← isTrue, cast_cast, cast_eq]
        subst actionEq
        have decision := (serviceRuntime setup mode deadline).serviceDecision_authentic_opening
            leaks control.execution inputs actor event payload binding checks outputEq
            codeEq node handle value associatedHandle handleOwner fixed active stored
        have materialEq : material =
            (disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor ((serviceApplication setup mode deadline leaks).observePlayer
                control.execution.application actor)
              (control.execution.network.known actor) := by
          have transmission := congrArg ReactiveApplication.Action.transmission decision
          unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision
            at transmission
          simp only [ite_eq_right activeView, node] at transmission
          rw [transmission] at submits
          cases submits
          rfl
        subst materialEq
        have packetEq : (serviceApplication setup mode deadline leaks).packet
            ((serviceApplication setup mode deadline leaks).submit control.execution.application
              actor
              ((disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
                actor ((serviceApplication setup mode deadline leaks).observePlayer
                  control.execution.application actor)
                (control.execution.network.known actor)))
            actor (control.execution.network.known actor)
            ((disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor ((serviceApplication setup mode deadline leaks).observePlayer
                control.execution.application actor)
              (control.execution.network.known actor)) =
              ⟨.opening event handle ⟨payload, value⟩, some ⟨handle, ⟨payload, value⟩⟩,
                control.execution.application.publicView.tokenFor
                  (.opening event handle ⟨payload, value⟩)⟩ := by
          have emitted := WitnessedSubmission.normalizeReactive_emit
              (serviceRuntime setup mode deadline) leaks control.execution.application actor
              (control.execution.network.known actor)
              (disclosureSubmission (.opening event handle ⟨payload, value⟩))
          have opened := (serviceRuntime setup mode deadline).windowOpening_packet leaks actor
              event handle ⟨payload, value⟩ control.execution.application
              (control.execution.network.known actor) handleOwner fixed
          exact emitted.trans opened
        rw [packetEq, control.execution.application.publicView_tokenFor_of_ready _ event rfl ready]
        apply ((serviceRuntime setup mode deadline).freshServiceAcceptable_opening_iff
                control.execution.application.publicView _ event actor payload binding checks
                outputEq codeEq node handle ⟨payload, value⟩
                (some ⟨handle, ⟨payload, value⟩⟩) _).mpr
        exact ⟨readyView, inTime, by simp only [certifiedOpening, decide_true], rfl,
          handleOwner, associatedHandle, rfl, rfl⟩
      · rw [packet] at submits
        cases submits

/-- **The recall entry of a canonical packet is a fresh call.** At every
history of the service runtime, the canonical decision of `who` at its turn
`event`, sent while an inclusion within `bound event` slots lands before the
deadline, is recorded by the response as a fresh call of `who` for `event`. -/
theorem canonical_freshCall {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (bound : (serviceGraph setup mode).EventId → Nat)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (fits : control.execution.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event)
    (action : (serviceGraph setup mode).Action event)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (submits : ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) event
      action).transmission = some material) :
    FreshCall setup leaks who event bound
      ⟨control.execution.observe (serviceApplication setup mode deadline leaks) who,
        (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
          (control.execution.recall who)
          (control.execution.observe (serviceApplication setup mode deadline leaks) who) event
          action,
        some ⟨(who, control.execution.network.nextSerial who),
          (serviceApplication setup mode deadline leaks).packet
            ((serviceApplication setup mode deadline leaks).submit control.execution.application
              who material) who (control.execution.network.known who) material⟩⟩
      ⟨(who, control.execution.network.nextSerial who),
        (serviceApplication setup mode deadline leaks).packet
          ((serviceApplication setup mode deadline leaks).submit control.execution.application
            who material) who (control.execution.network.known who) material⟩ := by
  have named : material.call.packet.event? (serviceGraph setup mode) = some event := by
    rcases (serviceRuntime setup mode deadline).canonicalServiceDecision_cases leaks who
        (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who) event
        action with silent | submitted
    · rw [silent] at submits
      cases submits
    · unfold EventGraphRuntime.submittedEvent? at submitted
      rw [submits] at submitted
      exact submitted
  exact
    { fresh := ⟨material, submits⟩
      emitted := rfl
      authored := rfl
      addressed := named
      ready := (PublicView.ownTurn?_spec _ who event turn).1
      fits := fits
      conforming := canonicalServiceDecision_freshServiceAcceptable trace who event turn
        fits.withinDeadline action material submits }

section OnePacket

variable [Fintype Player] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))

/-- **One packet per event.** At a history of the one-packet game of the
supplied runtime, under any scheduler, no entry of a player's recall emits a
packet for an event other than a given own packet for that event. -/
theorem onePacket_not_emitsOtherFor {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler} {control : (application setup
      runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (member : message ∈ (application setup runtime leaks).outputs (control.execution.recall who))
    (named : message.payload.call.event? (graph setup) = some event)
    (entry : (application setup runtime leaks).PlayerEntry) (_ : entry ∈ control.execution.recall
      who) :
    ¬ EmitsOtherFor runtime leaks entry event message.id := by
  rintro ⟨other, emitted, sender, otherNamed, different⟩
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have clean := (bounds.onePacketMenu_countClean runtime leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => runtime.countClean_initial leaks state)
    trace
  have recalled := clean.1
  have signed := signedCommitments_history runtime leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  -- Both packets are inputs of the network, signed by `who`.
  have messageSender : message.sender = who := by
    obtain ⟨recorded, recordedMember, recordedEmitted⟩ := List.mem_filterMap.mp member
    exact (signed.emissions who recorded recordedMember message recordedEmitted).1
  have otherMember : other ∈ (application setup runtime leaks).outputs (control.execution.recall
    who) :=
    List.mem_filterMap.mpr ⟨entry, by assumption, emitted⟩
  have inputOf (packet : Message Player (WitnessedPacket (graph setup)))
      (output : packet ∈ (application setup runtime leaks).outputs (control.execution.recall who)) :
      packet ∈ control.execution.network.inputs := by
    rw [← recalled.1 who] at output
    exact (List.mem_filter.mp output).1
  have otherSender : other.sender = who := sender.trans messageSender
  have serials : other.id.2 ≠ message.id.2 := by
    intro same
    apply different
    exact Prod.ext (otherSender.trans messageSender.symm) same
  -- The later of the two packets is not first for the event.
  have firstFor (packet earlierPacket : Message Player (WitnessedPacket (graph setup)))
      (packetInput : packet ∈ control.execution.network.inputs)
      (earlierInput : earlierPacket ∈ control.execution.network.inputs)
      (sameSender : earlierPacket.sender = packet.sender)
      (lower : earlierPacket.id.2 < packet.id.2) :
      earlierPacket.payload.call.event? (graph setup) ≠
        packet.payload.call.event? (graph setup) := by
    have permitted := (countPermits_eq_true_iff _ _).mp (clean.2 packet packetInput)
    exact permitted.2.2 earlierPacket ⟨earlierInput, sameSender, lower⟩
  rcases Nat.lt_or_gt_of_ne serials with lower | higher
  · exact firstFor message other (inputOf message member) (inputOf other otherMember)
      (otherSender.trans messageSender.symm) lower (otherNamed.trans named.symm)
  · exact firstFor other message (inputOf other otherMember) (inputOf message member)
      (messageSender.trans otherSender.symm) higher (named.trans otherNamed.symm)

end OnePacket

end Vegas
