/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalConformance
import Vegas.Game.OnePacketPrescribedSupport
import Vegas.Pending.ReactiveSignedCommitments

/-! # Canonical decisions are permitted first packets

At every history of the service runtime, under arbitrary responses and
scheduler choices, a canonical decision at the owner's turn for an event its
recall has not submitted for transmits a packet the count verdict permits
against the owner's earlier packets
(`Vegas.canonicalServiceDecision_countPermits`):

* its readiness token is the event's, which is ready;
* a commitment names a binding event of its sender, carries no evidence, and
  uses a prepared slot that is fresh, which no own commitment has named, since
  an own commitment fixes its handle;
* an opening carries its exact certificate, and opens the handle accepted for
  the binding: the fixed handle of an initial binding input, or a handle an own
  earlier commitment named for the binding event;
* no own earlier packet names the event, since the recall has not submitted for
  it.

So, at a one-packet history of the default runtime, every canonical decision
the canonical menu retains at a pending event lies in the one-packet menu
(`Vegas.canonical_mem_onePacket_of_pending`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The service's initial law consists of initial runtime states. -/
theorem serviceInitialLaw_initialized (state : EventGraphRuntime.State (serviceGraph setup mode))
    (supported : state ∈ (serviceInitialLaw setup mode).support) :
    ∃ inputs, state = EventGraphRuntime.State.initial inputs := by
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  exact ⟨_, rfl⟩

variable {setup leaks}

/-- An own output is an earlier own packet of every packet the owner emits
next. -/
theorem earlierOwnPacket_of_output {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (who : Player) (payload : WitnessedPacket (serviceGraph setup mode))
    (other : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (member : other ∈ (serviceApplication setup mode deadline leaks).outputs
      (control.execution.recall who)) :
    EarlierOwnPacket ((serviceApplication setup mode deadline leaks).outputs
        (control.execution.recall who))
      ⟨(who, control.execution.network.nextSerial who), payload⟩ other := by
  have recalled := (serviceRuntime setup mode deadline).countRecall_history leaks trace
  have signed := signedCommitments_history (serviceRuntime setup mode deadline) leaks
    (serviceInitialLaw setup mode) (serviceInitialLaw_initialized setup) horizon scheduler trace
  obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp member
  have sender := (signed.emissions who entry entryMember other emitted).1
  have input : other ∈ control.execution.network.inputs := by
    rw [← recalled.1 who] at member
    exact (List.mem_filter.mp member).1
  refine ⟨member, sender, ?_⟩
  have lower := recalled.2.2.serial_lt input
  rw [sender] at lower
  exact lower

/-- The packet any own output carries names the event its recalled
submission named. -/
theorem output_event {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (unsent : (serviceRuntime setup mode deadline).eventRecorded leaks
      (control.execution.recall who) event = false)
    (other : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (member : other ∈ (serviceApplication setup mode deadline leaks).outputs
      (control.execution.recall who)) :
    other.payload.call.event? (serviceGraph setup mode) ≠ some event := by
  have signed := signedCommitments_history (serviceRuntime setup mode deadline) leaks
    (serviceInitialLaw setup mode) (serviceInitialLaw_initialized setup) horizon scheduler trace
  obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp member
  obtain ⟨_, material, transmission, call⟩ := signed.emissions who entry entryMember other emitted
  have notSubmitted : (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action ≠
      some event := by
    intro submitted
    have recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (control.execution.recall who) event = true :=
      List.any_eq_true.mpr ⟨entry, entryMember, by simp [submitted]⟩
    rw [unsent] at recorded
    cases recorded
  intro named
  apply notSubmitted
  unfold EventGraphRuntime.submittedEvent?
  rw [transmission]
  change material.call.packet.event? (serviceGraph setup mode) = some event
  rw [← call]
  exact named

/-- **A canonical decision is a permitted first packet.** At every history of
the service runtime, under arbitrary responses and scheduler choices, the
canonical decision of `who` at its turn `event`, for which its recall has not
submitted, transmits a packet whose local envelope the count verdict permits
against `who`'s earlier packets. -/
theorem canonicalServiceDecision_countPermits {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : (serviceRuntime setup mode deadline).eventRecorded leaks
      (control.execution.recall who) event = false)
    (action : (serviceGraph setup mode).Action event)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (submits : ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) event
      action).transmission = some material) :
    countPermits ((serviceApplication setup mode deadline leaks).outputs
        (control.execution.recall who))
      ((serviceRuntime setup mode deadline).localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who)
        material) = true := by
  have recalled := (serviceRuntime setup mode deadline).countRecall_history leaks trace
  have signed := signedCommitments_history (serviceRuntime setup mode deadline) leaks
    (serviceInitialLaw setup mode) (serviceInitialLaw_initialized setup) horizon scheduler trace
  have facts := legalFacts setup leaks horizon scheduler control trace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (control.execution.application.publicView_eventReady event).mp readyView
  rw [(serviceRuntime setup mode deadline).localEnvelope_eq_of_recall leaks control.execution
    recalled.1 recalled.2.1 who material]
  -- The transmitted packet names the event.
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
  have packetCall : ((serviceApplication setup mode deadline leaks).packet
      ((serviceApplication setup mode deadline leaks).submit control.execution.application who
        material) who (control.execution.network.known who) material).call =
      material.call.packet := rfl
  have token : ((serviceApplication setup mode deadline leaks).packet
      ((serviceApplication setup mode deadline leaks).submit control.execution.application who
        material) who (control.execution.network.known who) material).token = some ⟨event⟩ := by
    rw [(serviceRuntime setup mode deadline).reactiveApplication_packet_token leaks]
    exact control.execution.application.publicView_tokenFor_of_ready _ event named ready
  apply (countPermits_eq_true_iff _ _).mpr
  refine ⟨(WitnessedPacket.tokenValid_iff _).mpr ⟨event, packetCall ▸ named, token⟩, ?_, ?_⟩
  rotate_left
  · intro other earlier
    change other.payload.call.event? (serviceGraph setup mode) ≠
      ((serviceApplication setup mode deadline leaks).packet
        ((serviceApplication setup mode deadline leaks).submit control.execution.application who
          material) who (control.execution.network.known who) material).call.event?
        (serviceGraph setup mode)
    rw [packetCall, named]
    exact output_event trace who event unsent other earlier.1
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind actor payload outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      generalize hview : control.execution.observe (serviceApplication setup mode deadline leaks)
        actor = view at submits
      cases selected : canonicalFreshSlot actor view.application with
      | none =>
          simp only [EventGraphRuntime.canonicalServiceDecision,
            EventGraphRuntime.canonicalReactiveDecision, node, selected, Option.map_none,
            ReactiveApplication.SubmissionNormalization.action] at submits
          cases submits
      | some serial =>
          have fresh := canonicalFreshSlot_spec actor _ serial selected
          rw [← hview] at fresh selected
          rw [← hview] at submits
          rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_binding leaks actor
            (control.execution.recall actor)
            (control.execution.observe (serviceApplication setup mode deadline leaks) actor) event
            payload outputEq codeEq node serial selected choice] at submits
          cases Option.some.inj submits
          rw [reactiveApplication_packet_none]
          refine ⟨?_, rfl, rfl, ⟨serial, rfl⟩, ?_⟩
          · have layout : setup.eventGraph.outputLayout event = .binding actor payload := outputEq
            simp [bindingOwnedBy, layout, Message.sender]
          · intro other earlier named sameCall
            exact signed.ownFixed actor other earlier.1 named (.prepared serial) sameCall fresh
  | resolve actor payload binding checks outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_eq_of_not_bind leaks actor
        (control.execution.recall actor)
        (control.execution.observe (serviceApplication setup mode deadline leaks) actor) event
        action
        (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at submits
      unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at submits
      simp only [node] at submits
      rcases reactiveResolutionPacket_shape actor event payload binding checks outputEq action
          (control.execution.observe (serviceApplication setup mode deadline leaks)
              actor).application with ⟨candidate, raw, packet⟩ | packet
      · obtain ⟨isTrue, value, localResolved, associated, handleOwner, rawEq⟩ :=
          reactiveResolutionPacket_opening actor event payload binding checks outputEq action
            (control.execution.observe (serviceApplication setup mode deadline leaks)
                actor).application event candidate raw packet
        subst rawEq
        have resolved : EventGraph.EventCode.resolveOutput? binding checks true
            control.execution.application.config.store = some (.success value) := by
          have local' := localResolved
          change EventGraph.EventCode.resolveOutput? binding checks true
            ((serviceGraph setup mode).playerStore actor
                control.execution.application.config.store) = _
            at local'
          rwa [EventGraph.EventCode.resolveOutput?_playerStore] at local'
        have stored := EventGraph.EventCode.binding_success_of_resolve_success binding checks
          true control.execution.application.config.store value resolved
        obtain ⟨handle, associatedHandle, _, fixed⟩ :=
          facts.binding.success_provenance binding value stored
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
        have decision := (serviceRuntime setup mode deadline).serviceDecision_successful_opening
            leaks control.execution facts.inputs actor event payload binding checks outputEq codeEq
                node
            handle value associatedHandle handleOwner fixed resolved
        have materialEq : material =
            (disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor ((serviceApplication setup mode deadline leaks).observePlayer
                  control.execution.application actor)
              (control.execution.network.known actor) := by
          have transmission := congrArg ReactiveApplication.Action.transmission decision
          unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision
            at transmission
          simp only [node] at transmission
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
          have packet := (serviceRuntime setup mode deadline).windowOpening_packet leaks actor event
              handle ⟨payload, value⟩ control.execution.application
                  (control.execution.network.known actor)
              handleOwner fixed
          exact emitted.trans packet
        rw [packetEq]
        refine ⟨by simp only [certifiedOpening, decide_true], ?_⟩
        simp only [node]
        refine ⟨by trivial, by trivial, ?_⟩
        cases field : binding.field with
        | inl input =>
            rw [field] at associatedHandle
            have slot := signed.inputHandles input handle associatedHandle
            change handle = (actor, .initial input)
            rw [← handleOwner, ← slot]
        | inr bindEvent =>
            rw [field] at associatedHandle
            obtain ⟨other, member, call⟩ := signed.acceptedSigned bindEvent handle associatedHandle
            rw [handleOwner] at member
            exact ⟨other, earlierOwnPacket_of_output trace actor _ other member, call⟩
      · rw [packet] at submits
        cases submits

section OnePacket

variable [Fintype Player] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))

/-- **Retained canonical decisions are one-packet responses.** At a history of
the one-packet game of the default runtime, under any scheduler, a canonical
decision of `who` at its turn `event`, for which its recall has not submitted,
lies in the one-packet menu whenever the canonical menu retains it. -/
theorem canonical_mem_onePacket_of_pending {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    (action : (graph setup).Action event)
    (retained : (runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event action ∈
      bounds.canonicalActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who)) :
    (runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event action ∈
      bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  exact canonical_mem_onePacket setup leaks bounds who _ _ _ retained fun material submits =>
    canonicalServiceDecision_countPermits rawTrace who event turn unsent action material submits

end OnePacket

end Vegas
