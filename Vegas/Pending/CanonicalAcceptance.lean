module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.RecordedCall
public import Vegas.Pending.ReactiveAssociationEvidence
public import Vegas.Pending.ReactiveGuardedResponse
public import Vegas.Pending.ReactiveAcceptedOutput
public import Vegas.Pending.ReactiveCanonicalMenu
public import Vegas.Pending.ReactiveOpeningWindow

@[expose] public section

/-! # Canonical graph packets and their exact native effects

A transmitting canonical decision fixes its graph action and actual typed result.
Authentic openings may publish failure when public guards reject them. At every
initialized raw history, a timely canonical packet is acceptable and its recorded
response is a protected fresh call, in every dependency choice.
-/
noncomputable section

namespace Vegas.EventGraphRuntime
open Interaction GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


variable {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => (reactiveApplication timeouts) leaks

variable {inputs : PMF graph.Inputs}

/-- **A canonical decision sent in time is acceptable.** At every history of
the service runtime, the canonical decision of `who` at its turn `event`,
within the event's deadline, transmits a packet the contract accepts on the
current view. -/
theorem canonicalServiceDecision_freshServiceAcceptable {horizon : Nat}
    {scheduler : (app).Scheduler}
    {control : (app).Control}
    (trace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace (some control))
    (who : Player) (event : graph.EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (within : control.execution.application.publicView.WithinDeadline
      timeouts event)
    (action : graph.Action event)
    (material : (app).Submission)
    (submits : (canonicalServiceDecision timeouts leaks who
      (control.execution.logs who)
      (control.execution.observe (app) who) event
      action).transmission = some material) :
    freshServiceAcceptable timeouts
      control.execution.application.publicView
      ⟨(who, control.execution.network.nextSerial who),
        (app).packet
          ((app).submit control.execution.application
            who material) who (control.execution.network.known who) material⟩ := by
  have bindingValid := reactiveBindingInvariant_history timeouts leaks inputs horizon scheduler
    trace
  have inputRecall := (app).history_inputRecall
    (inputs.map State.initial) horizon scheduler trace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (control.execution.application.publicView_eventReady event).mp readyView
  have activeView := (canonicalServiceDecision_active timeouts) leaks
    who (control.execution.logs who)
    (control.execution.observe (app) who)
    event action material submits
  have active : who ∉ control.execution.application.config.defaulted := activeView
  have inTime : (match control.execution.application.activatedAt event with
      | none => False
      | some entered => control.execution.application.clock - entered <
          timeouts.duration event) := within
  cases node : nodeView graph event with
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
          rw [(canonicalServiceDecision_binding_none timeouts) leaks
            actor _ _ event actor payload outputEq codeEq node] at submits
          cases submits
      | some choice =>
        cases selected : canonicalFreshSlot actor
            (control.execution.observe (app)
              actor).application with
        | none =>
            simp only [EventGraphRuntime.canonicalServiceDecision,
              EventGraphRuntime.canonicalReactiveDecision, ite_eq_right activeView,
              node, cast_cast, cast_eq, Option.bind_some, selected, Option.map_none,
              ReactiveApplication.SubmissionNormalization.action] at submits
            cases submits
        | some serial =>
            have fresh := canonicalFreshSlot_spec actor _ serial selected
            rw [(canonicalServiceDecision_binding timeouts) leaks actor
              (control.execution.logs actor)
              (control.execution.observe (app) actor) event
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
      rw [(canonicalServiceDecision_eq_of_not_bind timeouts) leaks
        actor
        (control.execution.logs actor)
        (control.execution.observe (app) actor) event
        action (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at submits
      unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at submits
      simp only [ite_eq_right activeView, node] at submits
      rcases reactiveResolutionPacket_shape actor event payload binding checks outputEq action
          (control.execution.observe (app)
            actor).application with ⟨candidate, raw, packet⟩ | packet
      · obtain ⟨_, isTrue, _, value, localStored, associated, handleOwner, rawEq⟩ :=
          reactiveResolutionPacket_opening_spec actor event payload binding checks outputEq action
            (control.execution.observe (app)
              actor).application event candidate raw packet
        subst rawEq
        have stored : binding.get? control.execution.application.config.store =
            some (.success value) := by
          change binding.get? (graph.playerStore actor
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
        have decision := (serviceDecision_authentic_opening timeouts)
            leaks control.execution inputRecall actor event payload binding checks outputEq
            codeEq node handle value associatedHandle handleOwner fixed active stored
        have materialEq : material =
            (disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor ((app).observePlayer
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
        have packetEq : (app).packet
            ((app).submit control.execution.application
              actor
              ((disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
                actor ((app).observePlayer
                  control.execution.application actor)
                (control.execution.network.known actor)))
            actor (control.execution.network.known actor)
            ((disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor ((app).observePlayer
                control.execution.application actor)
              (control.execution.network.known actor)) =
              ⟨.opening event handle ⟨payload, value⟩, some ⟨handle, ⟨payload, value⟩⟩,
                control.execution.application.publicView.tokenFor
                  (.opening event handle ⟨payload, value⟩)⟩ := by
          have emitted := WitnessedSubmission.normalizeReactive_emit
              timeouts leaks control.execution.application actor
              (control.execution.network.known actor)
              (disclosureSubmission (.opening event handle ⟨payload, value⟩))
          have opened := (windowOpening_packet timeouts) leaks actor
              event handle ⟨payload, value⟩ control.execution.application
              (control.execution.network.known actor) handleOwner fixed
          exact emitted.trans opened
        rw [packetEq, control.execution.application.publicView_tokenFor_of_ready _ event rfl ready]
        apply (freshServiceAcceptable_opening_iff timeouts
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
    {scheduler : (app).Scheduler}
    {control : (app).Control}
    (trace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace (some control))
    (bound : graph.EventId → Nat)
    (who : Player) (event : graph.EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (fits : control.execution.application.publicView.InclusionFitsDeadline
      timeouts bound event)
    (action : graph.Action event)
    (material : (app).Submission)
    (submits : (canonicalServiceDecision timeouts leaks who
      (control.execution.logs who)
      (control.execution.observe (app) who) event
      action).transmission = some material) :
    FreshCall timeouts leaks who event bound
      ⟨control.execution.observe (app) who,
        canonicalServiceDecision timeouts leaks who
          (control.execution.logs who)
          (control.execution.observe (app) who) event
          action,
        some ⟨(who, control.execution.network.nextSerial who),
          (app).packet
            ((app).submit control.execution.application
              who material) who (control.execution.network.known who) material⟩⟩
      ⟨(who, control.execution.network.nextSerial who),
        (app).packet
          ((app).submit control.execution.application
            who material) who (control.execution.network.known who) material⟩ := by
  have named : material.call.packet.event? graph = some event := by
    rcases (canonicalServiceDecision_cases timeouts) leaks who
        (control.execution.logs who)
        (control.execution.observe (app) who) event
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

/-- A transmitting canonical decision fixes its actual graph action and typed output. -/
theorem canonical_response_witness
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (event : graph.EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (action : graph.Action event) (material :
      ((reactiveApplication timeouts) leaks).Submission)
    (submits : ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
      (execution.observe ((reactiveApplication timeouts) leaks) who) event action).transmission =
        some material) :
    ∃ output, AcceptanceWitness event (sentEnvelope timeouts leaks execution who material)
      execution.application.config action output
      (((reactiveApplication timeouts) leaks).submit execution.application who material) := by
  have activeView := (canonicalServiceDecision_active timeouts) leaks who (execution.logs who)
    (execution.observe ((reactiveApplication timeouts) leaks) who) event action material submits
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  cases node : nodeView graph event with
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
                (graph.nodes event),
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

end Vegas.EventGraphRuntime
