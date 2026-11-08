/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFreshCall
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Pending.ReactiveAcceptedOutput
import Vegas.Pending.ReactiveCanonicalMenu
import Vegas.Pending.ReactiveOpeningWindow

/-! # Canonical source packets and their exact native effects

A transmitting canonical decision fixes its graph action and actual typed result.
Authentic openings may publish failure when public guards reject them. At every
initialized raw history, a timely canonical packet is acceptable and its recorded
response is a protected fresh call, in every dependency mode.
-/
noncomputable section

namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]



section Admission
variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **A canonical decision sent in time is acceptable.** At every history of
the service runtime, the canonical decision of `who` at its turn `event`,
within the event's deadline, transmits a packet the contract accepts on the
current view. -/
theorem canonicalServiceDecision_freshServiceAcceptable {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {control : (serviceApplication setup mode duration leaks).Control}
    (trace : ((serviceApplication setup mode duration leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (within : control.execution.application.publicView.WithinDeadline
      (serviceTimeouts setup mode duration) event)
    (action : (serviceGraph setup mode).Action event)
    (material : (serviceApplication setup mode duration leaks).Submission)
    (submits : ((canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks who
      (control.execution.logs who)
      (control.execution.observe (serviceApplication setup mode duration leaks) who) event
      action).transmission = some material) :
    (freshServiceAcceptable (serviceTimeouts setup mode duration))
      control.execution.application.publicView
      ⟨(who, control.execution.network.nextSerial who),
        (serviceApplication setup mode duration leaks).packet
          ((serviceApplication setup mode duration leaks).submit control.execution.application
            who material) who (control.execution.network.known who) material⟩ := by
  have bindingValid := ((reactiveBindingInvariant (serviceTimeouts setup mode duration))
    leaks).history
    (serviceInitialLaw setup mode) horizon scheduler (fun state member => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
      exact State.initial_bindingInvariant _) trace
  have inputs := (serviceApplication setup mode duration leaks).history_inputRecall
    (serviceInitialLaw setup mode) horizon scheduler trace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (control.execution.application.publicView_eventReady event).mp readyView
  have activeView := (canonicalServiceDecision_active (serviceTimeouts setup mode duration)) leaks
    who (control.execution.logs who)
    (control.execution.observe (serviceApplication setup mode duration leaks) who)
    event action material submits
  have active : who ∉ control.execution.application.config.defaulted := activeView
  have inTime : (match control.execution.application.activatedAt event with
      | none => False
      | some entered => control.execution.application.clock - entered <
          (serviceTimeouts setup mode duration).duration event) := within
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
          rw [(canonicalServiceDecision_binding_none (serviceTimeouts setup mode duration)) leaks
            actor _ _ event actor payload outputEq codeEq node] at submits
          cases submits
      | some choice =>
        cases selected : canonicalFreshSlot actor
            (control.execution.observe (serviceApplication setup mode duration leaks)
              actor).application with
        | none =>
            simp only [EventGraphRuntime.canonicalServiceDecision,
              EventGraphRuntime.canonicalReactiveDecision, ite_eq_right activeView,
              node, cast_cast, cast_eq, Option.bind_some, selected, Option.map_none,
              ReactiveApplication.SubmissionNormalization.action] at submits
            cases submits
        | some serial =>
            have fresh := canonicalFreshSlot_spec actor _ serial selected
            rw [(canonicalServiceDecision_binding (serviceTimeouts setup mode duration)) leaks actor
              (control.execution.logs actor)
              (control.execution.observe (serviceApplication setup mode duration leaks) actor) event
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
      rw [(canonicalServiceDecision_eq_of_not_bind (serviceTimeouts setup mode duration)) leaks
        actor
        (control.execution.logs actor)
        (control.execution.observe (serviceApplication setup mode duration leaks) actor) event
        action (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at submits
      unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at submits
      simp only [ite_eq_right activeView, node] at submits
      rcases reactiveResolutionPacket_shape actor event payload binding checks outputEq action
          (control.execution.observe (serviceApplication setup mode duration leaks)
            actor).application with ⟨candidate, raw, packet⟩ | packet
      · obtain ⟨_, isTrue, _, value, localStored, associated, handleOwner, rawEq⟩ :=
          reactiveResolutionPacket_opening_spec actor event payload binding checks outputEq action
            (control.execution.observe (serviceApplication setup mode duration leaks)
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
        have decision := (serviceDecision_authentic_opening (serviceTimeouts setup mode duration))
            leaks control.execution inputs actor event payload binding checks outputEq
            codeEq node handle value associatedHandle handleOwner fixed active stored
        have materialEq : material =
            (disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor ((serviceApplication setup mode duration leaks).observePlayer
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
        have packetEq : (serviceApplication setup mode duration leaks).packet
            ((serviceApplication setup mode duration leaks).submit control.execution.application
              actor
              ((disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
                actor ((serviceApplication setup mode duration leaks).observePlayer
                  control.execution.application actor)
                (control.execution.network.known actor)))
            actor (control.execution.network.known actor)
            ((disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor ((serviceApplication setup mode duration leaks).observePlayer
                control.execution.application actor)
              (control.execution.network.known actor)) =
              ⟨.opening event handle ⟨payload, value⟩, some ⟨handle, ⟨payload, value⟩⟩,
                control.execution.application.publicView.tokenFor
                  (.opening event handle ⟨payload, value⟩)⟩ := by
          have emitted := WitnessedSubmission.normalizeReactive_emit
              (serviceTimeouts setup mode duration) leaks control.execution.application actor
              (control.execution.network.known actor)
              (disclosureSubmission (.opening event handle ⟨payload, value⟩))
          have opened := (windowOpening_packet (serviceTimeouts setup mode duration)) leaks actor
              event handle ⟨payload, value⟩ control.execution.application
              (control.execution.network.known actor) handleOwner fixed
          exact emitted.trans opened
        rw [packetEq, control.execution.application.publicView_tokenFor_of_ready _ event rfl ready]
        apply ((freshServiceAcceptable_opening_iff (serviceTimeouts setup mode duration))
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
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {control : (serviceApplication setup mode duration leaks).Control}
    (trace : ((serviceApplication setup mode duration leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (bound : (serviceGraph setup mode).EventId → Nat)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (fits : control.execution.application.publicView.InclusionFitsDeadline
      (serviceTimeouts setup mode duration) bound event)
    (action : (serviceGraph setup mode).Action event)
    (material : (serviceApplication setup mode duration leaks).Submission)
    (submits : ((canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks who
      (control.execution.logs who)
      (control.execution.observe (serviceApplication setup mode duration leaks) who) event
      action).transmission = some material) :
    FreshCall setup leaks who event bound
      ⟨control.execution.observe (serviceApplication setup mode duration leaks) who,
        (canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks who
          (control.execution.logs who)
          (control.execution.observe (serviceApplication setup mode duration leaks) who) event
          action,
        some ⟨(who, control.execution.network.nextSerial who),
          (serviceApplication setup mode duration leaks).packet
            ((serviceApplication setup mode duration leaks).submit control.execution.application
              who material) who (control.execution.network.known who) material⟩⟩
      ⟨(who, control.execution.network.nextSerial who),
        (serviceApplication setup mode duration leaks).packet
          ((serviceApplication setup mode duration leaks).submit control.execution.application
            who material) who (control.execution.network.known who) material⟩ := by
  have named : material.call.packet.event? (serviceGraph setup mode) = some event := by
    rcases (canonicalServiceDecision_cases (serviceTimeouts setup mode duration)) leaks who
        (control.execution.logs who)
        (control.execution.observe (serviceApplication setup mode duration leaks) who) event
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
end Admission

section Witness
variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {timeouts : EventTimeouts (serviceGraph setup mode)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A transmitting canonical decision fixes its actual graph action and typed output. -/
theorem canonical_response_witness
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (action : (serviceGraph setup mode).Action event) (material :
      ((reactiveApplication timeouts) leaks).Submission)
    (submits : ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
      (execution.observe ((reactiveApplication timeouts) leaks) who) event action).transmission =
        some material) :
    ∃ output, AcceptanceWitness event (sentEnvelope setup timeouts leaks execution who material)
      execution.application.config action output
      (((reactiveApplication timeouts) leaks).submit execution.application who material) := by
  have activeView := (canonicalServiceDecision_active timeouts) leaks who (execution.logs who)
    (execution.observe ((reactiveApplication timeouts) leaks) who) event action material submits
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
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
          rw [(canonicalServiceDecision_binding_none timeouts) leaks actor _ _ event actor payload
            outputEq codeEq node] at submits
          cases submits
      | some choice =>
          cases selected : canonicalFreshSlot actor
              (execution.observe ((reactiveApplication timeouts) leaks) actor).application with
          | none =>
              simp only [EventGraphRuntime.canonicalServiceDecision,
                EventGraphRuntime.canonicalReactiveDecision, ite_eq_right activeView,
                node, cast_cast, cast_eq, Option.bind_some, selected, Option.map_none,
                ReactiveApplication.SubmissionNormalization.action] at submits
              cases submits
          | some serial =>
              have fresh := canonicalFreshSlot_spec actor _ serial selected
              rw [(canonicalServiceDecision_binding timeouts) leaks actor (execution.logs actor)
                (execution.observe ((reactiveApplication timeouts) leaks) actor) event payload
                outputEq codeEq node activeView serial selected choice] at submits
              cases Option.some.inj submits
              have freshLookup : execution.application.candidates.lookup
                  (actor, .prepared serial) = .fresh := fresh
              have meaning := (reactiveBinding_result timeouts) leaks actor event payload choice
                serial execution freshLookup
              refine ⟨cast (congrArg EventGraph.EventField.Value outputEq.symm) choice,
                Or.inl ⟨(actor, .prepared serial), actor, payload, outputEq, rfl, ?_, ?_, ?_⟩⟩
              · exact submitStep_commitment_fixed _ actor event (.prepared serial)
              · exact congrArg (fun result => cast
                  (congrArg EventGraph.EventField.Action outputEq.symm) (some result)) meaning.symm
              · exact congrArg (cast (congrArg EventGraph.EventField.Value outputEq.symm))
                  meaning.symm
  | resolve actor payload binding checks outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      rw [(canonicalServiceDecision_eq_of_not_bind timeouts) leaks actor (execution.logs actor)
        (execution.observe ((reactiveApplication timeouts) leaks) actor) event action
        (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at submits
      unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at submits
      simp only [ite_eq_right activeView, node] at submits
      rcases reactiveResolutionPacket_shape actor event payload binding checks outputEq action
          (execution.observe ((reactiveApplication timeouts) leaks) actor).application with
        ⟨candidate, raw, packet⟩ | packet
      · obtain ⟨_, isTrue, _, value, _, _, _, rawEq⟩ :=
          reactiveResolutionPacket_opening_spec actor event payload binding checks outputEq action
            (execution.observe ((reactiveApplication timeouts) leaks) actor).application event
            candidate raw packet
        subst rawEq
        have defined := EventGraph.EventCode.resolveOutput?_isSome binding checks true
          execution.application.config.store (fun field read =>
            execution.application.config.read_available ready (by
              rw [← EventGraph.EventCode.readFields_cast outputEq
                ((serviceGraph setup mode).nodes event),
                codeEq]
              exact read))
        let result := (EventGraph.EventCode.resolveOutput? binding checks true
          execution.application.config.store).get defined
        have resolved : EventGraph.EventCode.resolveOutput? binding checks true
            execution.application.config.store = some result := (Option.some_get defined).symm
        have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
            true := by
          rw [← isTrue, cast_cast, cast_eq]
        rw [packet] at submits
        simp only [Option.map_some, ReactiveApplication.SubmissionNormalization.action,
          Option.some.injEq] at submits
        refine ⟨cast (congrArg EventGraph.EventField.Value outputEq.symm) result,
          Or.inr ⟨candidate, ⟨payload, value⟩, actor, payload, binding, checks, outputEq,
            codeEq, result, ?_, node, resolved, actionEq, rfl⟩⟩
        rw [← submits]
        rfl
      · rw [packet] at submits
        cases submits

end Witness
end Vegas
