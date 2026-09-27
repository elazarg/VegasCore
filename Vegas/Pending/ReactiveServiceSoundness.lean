/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceConformance
import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Pending.ReactiveOpeningWindow
import Vegas.EventGraph.ResolutionProvenance
import Interaction.ReactiveTrafficAudit

/-! # Public audit soundness for retained service responses

The checker accepts transport of permitted known envelopes and each first
canonical service decision. The local hypotheses are operational phase facts:
readiness, deadline, binding allocation and the public serial count. They do
not select an equilibrium or require an auditor to inspect hidden material.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A completed phase whose envelopes are all published supplies the next
phase's conformance invariant for every public grant and clock value. -/
theorem service_published_conformance
    (execution : (runtime.reactiveApplication leaks).Execution)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id) :
    execution.network.Satisfies fun message => runtime.permittedServiceEnvelope
      execution.application.publicView execution.network.ledger message = true :=
  published.mono fun message present =>
    runtime.permittedServiceEnvelope_published _ _ message present

/-- Passive observations preserve conformance, including observations of a
current permitted envelope that has not yet reached the ledger. -/
theorem service_sampled_conformance
    (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (selected : Finset (MessageId Player))
    (prior : execution.network.Satisfies fun message => runtime.permittedServiceEnvelope
      execution.application.publicView execution.network.ledger message = true) :
    let next := execution.sampledActivation (runtime.reactiveApplication leaks) who selected
    next.network.Satisfies fun message => runtime.permittedServiceEnvelope
      next.application.publicView next.network.ledger message = true :=
  prior.learn who selected

/-- The actual transmitted record is sufficient to maintain conformance of
every retained network copy. Responses change neither the public phase nor
the ledger, even when they allocate private commitment material. -/
theorem service_response_conformance
    (execution : (runtime.reactiveApplication leaks).Execution)
    (remaining : Nat) (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (prior : execution.network.Satisfies fun message => runtime.permittedServiceEnvelope
      execution.application.publicView execution.network.ledger message = true)
    (issued : ∀ record ∈ (runtime.reactiveApplication leaks).trafficStep
      (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond (runtime.reactiveApplication leaks) who response⟩),
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true) :
    let next := execution.respond (runtime.reactiveApplication leaks) who response
    next.network.Satisfies fun message => runtime.permittedServiceEnvelope
      next.application.publicView next.network.ledger message = true := by
  intro next
  let app := runtime.reactiveApplication leaks
  have observed := (runtime.reactive_respond_application leaks execution who response).2
  have ledger : next.network.ledger = execution.network.ledger := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some transmission =>
        cases transmission with
        | submit submission => rfl
        | replay id =>
            change (execution.network.replay who id).2.ledger = execution.network.ledger
            unfold MessageNetwork.replay
            split <;> rfl
  change next.application.publicView = execution.application.publicView at observed
  rw [observed, ledger]
  apply app.trafficStep_network execution remaining who response _ prior
  intro record member
  have permitted := issued record member
  simp only [ReactiveApplication.trafficStep] at member
  obtain ⟨input, _, rfl⟩ := List.mem_map.mp member
  exact permitted

/-- Replaying a conforming pending envelope preserves its permission; ledger
publication is not needed. Silence and unknown replay ids produce no record. -/
theorem service_transport_traffic
    (execution : (runtime.reactiveApplication leaks).Execution)
    (remaining : Nat) (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (known : ∀ message ∈ execution.network.known who,
      runtime.permittedServiceEnvelope execution.application.publicView
        execution.network.ledger message = true) :
    ∀ record ∈ (runtime.reactiveApplication leaks).trafficStep
      (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond (runtime.reactiveApplication leaks) who response⟩),
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  intro record member
  obtain ⟨observation, ledger, present⟩ :=
    (runtime.reactiveApplication leaks).trafficStep_transport execution remaining who response
      transport record member
  rw [observation, ledger]
  exact known record.input.envelope present

/-- Canonical binding traffic passes public conformance for arbitrary private
opening material. The public checker does not promise later openability. -/
theorem service_binding_traffic
    (execution : (runtime.reactiveApplication leaks).Execution)
    (remaining : Nat) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (unused : execution.application.HandleUnused
      (owner, .prepared (execution.application.publicView.bindingCount owner)))
    (vacant : execution.application.accepted (.inr event) = none)
    (counted : execution.network.nextSerial owner =
      execution.network.ledger.countP (fun message => message.sender = owner))
    (opening : Option (Raw L)) :
    let app := runtime.reactiveApplication leaks
    let response : app.Action := ⟨some (.submit
      ⟨⟨.commitment event
        (owner, .prepared (execution.application.publicView.bindingCount owner)), opening⟩,
        .none⟩)⟩
    ∀ record ∈ app.trafficStep (some ⟨remaining, some owner, execution⟩)
      (some ⟨remaining, none, execution.respond app owner response⟩),
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  intro app response record member
  rw [app.trafficStep_submit, List.mem_singleton] at member
  subst record
  apply runtime.permittedServiceEnvelope_binding execution.application owner event
    execution.network.ledger (execution.network.nextSerial owner) granted _ counted
  simp only [PublicView.BindingIncludable, node]
  exact ⟨(execution.application.publicView_eventReady event).mpr ready, timely,
    by trivial, by trivial, vacant, unused⟩

/-- A successful guarded disclosure carries its matching certificate and
passes the public guard test, including after evidence normalization. -/
theorem service_opening_traffic
    (execution : (runtime.reactiveApplication leaks).Execution)
    (remaining : Nat) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (candidate : Handle graph) (value : L.Val payload)
    (associated : execution.application.accepted binding.field = some candidate)
    (owned : candidate.1 = owner)
    (fixed : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (resolved : EventCode.resolveOutput? binding checks true execution.application.config.store =
      some (.success value))
    (counted : execution.network.nextSerial owner =
      execution.network.ledger.countP (fun message => message.sender = owner)) :
    let app := runtime.reactiveApplication leaks
    let submission := WitnessedSubmission.normalizeReactive owner
      (app.observePlayer execution.application owner) (execution.network.known owner)
        (disclosureSubmission (.opening event candidate ⟨payload, value⟩))
    ∀ record ∈ app.trafficStep (some ⟨remaining, some owner, execution⟩)
      (some ⟨remaining, none, execution.respond app owner ⟨some (.submit submission)⟩⟩),
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  intro app submission record member
  have emitted := WitnessedSubmission.normalizeReactive_emit runtime leaks execution.application
    owner (execution.network.known owner)
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩))
  have packet := runtime.windowOpening_packet leaks owner event candidate ⟨payload, value⟩
    execution.application (execution.network.known owner) owned fixed
  change app.packet (app.submit execution.application owner submission) owner
    (execution.network.known owner) submission = _ at emitted
  have emittedPacket := emitted.trans packet
  rw [app.trafficStep_submit, List.mem_singleton] at member
  subst record
  change runtime.permittedServiceEnvelope execution.application.publicView execution.network.ledger
    ⟨(owner, execution.network.nextSerial owner), app.packet
      (app.submit execution.application owner submission) owner
        (execution.network.known owner) submission⟩ = true
  rw [emittedPacket, runtime.permittedServiceEnvelope_iff]
  refine Or.inr ⟨counted, ?_⟩
  apply (runtime.freshServiceEnvelope_opening_iff execution.application.publicView
    (owner, execution.network.nextSerial owner) event owner payload binding checks outputEq codeEq
      node candidate ⟨payload, value⟩ (some ⟨candidate, ⟨payload, value⟩⟩)).mpr
  refine ⟨granted, (execution.application.publicView_eventReady event).mpr ready, timely,
    by simp only [certifiedOpening, decide_true], ?_, rfl, owned, associated, rfl⟩
  apply (execution.application.publicView.openingGuardsAccepted_iff owner event payload binding
    checks outputEq codeEq node candidate ⟨payload, value⟩ _).mpr
  refine ⟨value, rfl, ?_⟩
  change GuardCheck.allAccepted? checks (graph.publicStore execution.application.config.store)
    (.success value) = some true
  rw [GuardCheck.allAccepted?_publicStore]
  exact EventCode.guards_pass_of_resolve_success binding checks true
    execution.application.config.store value resolved

/-- Both disclosure choices pass the checker. Failed validation and deliberate
withholding produce silence, while successful disclosure is certified. -/
theorem serviceDecision_resolution_traffic
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (invariant : execution.application.BindingInvariant)
    (remaining : Nat) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (counted : runtime.eventRecorded leaks (execution.recall owner) event = false →
      execution.network.nextSerial owner =
        execution.network.ledger.countP (fun message => message.sender = owner))
    (choice : Bool)
    (first : runtime.firstSubmission leaks (execution.recall owner)
      (runtime.serviceDecision leaks owner (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner) event
          (cast (congrArg EventField.Action outputEq.symm) choice)) = true) :
    let app := runtime.reactiveApplication leaks
    let response := runtime.serviceDecision leaks owner (execution.recall owner)
      (execution.observe app owner) event (cast (congrArg EventField.Action outputEq.symm) choice)
    ∀ record ∈ app.trafficStep (some ⟨remaining, some owner, execution⟩)
      (some ⟨remaining, none, execution.respond app owner response⟩),
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  intro app response
  cases choice with
  | false =>
      have quiet : response = ⟨none⟩ := by
        simp only [response, serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
          cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
          disclosureSubmission_normalize_withhold]
        rfl
      rw [quiet, app.trafficStep_silent]
      exact fun _ member => (List.not_mem_nil member).elim
  | true =>
      rcases runtime.serviceDecision_resolution_cases leaks owner _ _ event owner payload binding
        checks outputEq codeEq node true with quiet |
          ⟨candidate, value, evidence, resolved, associated, owned, shape⟩
      · change response = ⟨none⟩ at quiet
        rw [quiet, app.trafficStep_silent]
        exact fun _ member => (List.not_mem_nil member).elim
      · change EventCode.resolveOutput? binding checks true
          (graph.playerStore owner execution.application.config.store) = _ at resolved
        rw [EventCode.resolveOutput?_playerStore] at resolved
        have stored := EventCode.binding_success_of_resolve_success binding checks true
          execution.application.config.store value resolved
        obtain ⟨actual, accepted, _, fixed⟩ := invariant.success_provenance binding value stored
        change execution.application.accepted binding.field = some candidate at associated
        cases Option.some.inj (accepted.symm.trans associated)
        have serial := counted (by
          rw [shape] at first
          simpa only [firstSubmission, submittedEvent?, Payload.event?,
            Bool.not_eq_true_eq_eq_false] using first)
        have action := runtime.serviceDecision_successful_opening leaks execution recalled owner
          event payload binding checks outputEq codeEq node candidate value associated owned fixed
            resolved
        change response = _ at action
        rw [action]
        exact runtime.service_opening_traffic leaks execution remaining owner event payload binding
          checks outputEq codeEq node granted ready timely candidate value associated owned fixed
            resolved serial

variable [Fintype Player]

/-- All ordinary retained binding responses pass the checker, including
arbitrarily many waits and known replays before or after first submission. -/
theorem MessageBounds.compiled_binding_traffic (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.BindingInvariant)
    (remaining : Nat) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (freshSlot : runtime.eventRecorded leaks (execution.recall owner) event = false →
      reactiveFreshSlot (execution.observe (runtime.reactiveApplication leaks) owner).application =
        some (execution.application.publicView.bindingCount owner))
    (counted : runtime.eventRecorded leaks (execution.recall owner) event = false →
      execution.network.nextSerial owner =
        execution.network.ledger.countP (fun message => message.sender = owner))
    (known : ∀ message ∈ execution.network.known owner,
      runtime.permittedServiceEnvelope execution.application.publicView
        execution.network.ledger message = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks owner (execution.recall owner)
      (execution.observe (runtime.reactiveApplication leaks) owner)) :
    ∀ record ∈ (runtime.reactiveApplication leaks).trafficStep
      (some ⟨remaining, some owner, execution⟩)
      (some ⟨remaining, none,
        execution.respond (runtime.reactiveApplication leaks) owner response⟩),
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  let app := runtime.reactiveApplication leaks
  have owned : graph.actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
    exact actor
  have publicReady := (execution.application.publicView_eventReady event).mpr ready
  cases recorded : runtime.eventRecorded leaks (execution.recall owner) event with
  | true =>
      have replay := bounds.ordinary_binding_recorded runtime leaks owner _ _ event payload
        outputEq codeEq node granted owned publicReady recorded response member
      exact runtime.service_transport_traffic leaks execution remaining owner response
        (app.replayPolicy_cases _ _ response replay) known
  | false =>
      have slot := freshSlot recorded
      rcases bounds.ordinary_binding_cases runtime leaks owner _ _ event payload outputEq codeEq
        node granted owned publicReady _ slot response member with replay | ⟨value, _, _, rfl⟩
      · exact runtime.service_transport_traffic leaks execution remaining owner _
          (app.replayPolicy_cases _ _ _ replay) known
      · have fresh := reactiveFreshSlot_spec
          (execution.observe app owner).application _ slot
        rw [runtime.reactiveBinding_normal_of_fresh leaks owner _ _ event payload
          (.success value) _ fresh]
        have unused : execution.application.HandleUnused
            (owner, .prepared (execution.application.publicView.bindingCount owner)) :=
          fun field associated => invariant.accepted_fixed field _ associated fresh
        have vacant : execution.application.accepted (.inr event) = none := by
          cases associated : execution.application.accepted (.inr event) with
          | none => rfl
          | some candidate => exact False.elim (ready.1
              (invariant.toAssociationInvariant.accepted_complete event candidate associated))
        exact runtime.service_binding_traffic leaks execution remaining owner event payload outputEq
          codeEq node granted ready timely unused vacant (counted recorded) (some ⟨payload, value⟩)

/-- Every retained response by the resolution owner is permitted, independently
of the source profile and the probabilities it assigns to disclosure. -/
theorem MessageBounds.compiled_resolution_traffic (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (invariant : execution.application.BindingInvariant)
    (remaining : Nat) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (counted : runtime.eventRecorded leaks (execution.recall owner) event = false →
      execution.network.nextSerial owner =
        execution.network.ledger.countP (fun message => message.sender = owner))
    (known : ∀ message ∈ execution.network.known owner,
      runtime.permittedServiceEnvelope execution.application.publicView
        execution.network.ledger message = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks owner (execution.recall owner)
      (execution.observe (runtime.reactiveApplication leaks) owner)) :
    ∀ record ∈ (runtime.reactiveApplication leaks).trafficStep
      (some ⟨remaining, some owner, execution⟩)
      (some ⟨remaining, none,
        execution.respond (runtime.reactiveApplication leaks) owner response⟩),
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  classical
  let app := runtime.reactiveApplication leaks
  have owned : graph.actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
    exact actor
  have publicReady := (execution.application.publicView_eventReady event).mpr ready
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | replay
  · obtain ⟨chosen, first⟩ := Finset.mem_filter.mp decision
    have grantedView : (execution.observe app owner).application.publicView.serviceGrant =
        some event := granted
    have readyView : (execution.observe app owner).application.publicView.EventReady event :=
      publicReady
    dsimp only [app] at grantedView readyView
    simp only [MessageBounds.decisionActions, grantedView, owned, readyView,
      and_self, ↓reduceIte, node] at chosen
    obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp chosen
    exact runtime.serviceDecision_resolution_traffic leaks execution recalled invariant remaining
      owner event payload binding checks outputEq codeEq node granted ready timely counted choice
        first
  · exact runtime.service_transport_traffic leaks execution remaining owner response
      (app.replayPolicy_cases _ _ response (FinDist.mem_supportFinset.mp replay)) known

/-- Other participants can wait or replay during this event. The statement also
covers every participant at a chance event, whose actor is absent. -/
theorem MessageBounds.compiled_foreign_traffic (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (remaining : Nat) (who : Player) (event : graph.EventId)
    (granted : execution.application.serviceGrant = some event)
    (foreign : graph.actor? event ≠ some who)
    (known : ∀ message ∈ execution.network.known who,
      runtime.permittedServiceEnvelope execution.application.publicView
        execution.network.ledger message = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)) :
    ∀ record ∈ (runtime.reactiveApplication leaks).trafficStep
      (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond (runtime.reactiveApplication leaks) who response⟩),
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  have replay := bounds.compiled_foreign_transport runtime leaks who _ _ event granted foreign
    response member
  exact runtime.service_transport_traffic leaks execution remaining who response
    ((runtime.reactiveApplication leaks).replayPolicy_cases _ _ response replay) known

end Vegas.EventGraphRuntime
