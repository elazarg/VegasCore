/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceConformance
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Pending.ReactiveEvidence

/-! # Publicly conforming guarded openings execute successfully

The public service predicate does not inspect private binding material.
Authenticity of emitted evidence and the actual binding invariant discharge
that hidden part of the handler precondition. This connects the public audit
rule to the existing successful source disclosure response.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- At an actual execution, a conforming guarded opening is accepted. Neither
an unobservable validity promise nor a source strategy appears in the premise. -/
theorem service_opening_accepted
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (sound : (runtime.packetEvidence leaks).Sound execution)
    (invariant : execution.application.BindingInvariant)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (submission : WitnessedSubmission graph)
    (named : (submission.emit ((runtime.reactiveApplication leaks).submit execution.application
      owner submission) owner (execution.network.known owner)).call.event? graph = some event)
    (permitted : runtime.freshServiceEnvelope execution.application.publicView
      ⟨(owner, execution.network.nextSerial owner), submission.emit
        ((runtime.reactiveApplication leaks).submit execution.application owner submission)
          owner (execution.network.known owner)⟩) :
    ∃ next, (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit execution.application owner submission)
      ⟨(owner, execution.network.nextSerial owner), submission.emit
        ((runtime.reactiveApplication leaks).submit execution.application owner submission)
          owner (execution.network.known owner)⟩ = some next := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨candidate, raw, _, owned, associated, _, emitted, guards⟩ :=
    runtime.freshServiceEnvelope_resolution_shape execution.application.publicView owner event
      payload binding checks outputEq codeEq node _ named permitted
  change submission.emit (app.submit execution.application owner submission) owner
    (execution.network.known owner) =
      ⟨.opening event candidate raw, some ⟨candidate, raw⟩, some ⟨event⟩⟩ at emitted
  change execution.application.publicView.openingGuardsAccepted
    (submission.emit (app.submit execution.application owner submission) owner
      (execution.network.known owner)) = true at guards
  have call := congrArg WitnessedPacket.call emitted
  change submission.call.packet = .opening event candidate raw at call
  have unchanged : app.submit execution.application owner submission = execution.application := by
    rcases submission with ⟨⟨packet, material⟩, request⟩
    dsimp only at call
    subst packet
    cases material <;> rfl
  rw [emitted] at permitted
  obtain ⟨ready, timely, _, _, _, _, _, _, _⟩ :=
    (runtime.freshServiceEnvelope_opening_iff execution.application.publicView
      (owner, execution.network.nextSerial owner) event owner payload binding checks outputEq
        codeEq node candidate raw (some ⟨candidate, raw⟩) _).mp permitted
  rw [emitted] at guards
  obtain ⟨value, rawEq, publicChecks⟩ :=
    (execution.application.publicView.openingGuardsAccepted_iff owner event payload binding checks
      outputEq codeEq node candidate raw (some ⟨candidate, raw⟩)).mp guards
  subst raw
  have carried := congrArg WitnessedPacket.evidence emitted
  rw [unchanged] at carried
  have valid := submission.emit_sound execution.application owner (execution.network.known owner)
    (fun message member fact evidence => sound.known owner message member fact (by
      simp only [packetEvidence, evidence, Option.toList_some, List.mem_singleton]))
    ⟨candidate, ⟨payload, value⟩⟩ carried
  change execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ at valid
  have stored := invariant.opening_stored binding candidate value associated valid
  have acceptedChecks : GuardCheck.allAccepted? checks execution.application.config.store
      (.success value) = some true := by
    change GuardCheck.allAccepted? checks (graph.publicStore execution.application.config.store)
      (.success value) = some true at publicChecks
    rwa [GuardCheck.allAccepted?_publicStore] at publicChecks
  have resolved : EventCode.resolveOutput? binding checks true execution.application.config.store =
      some (.success value) := by
    simp only [EventCode.resolveOutput?, stored, Option.bind_eq_bind, Option.bind_some,
      ↓reduceIte, acceptedChecks, Option.pure_def]
  change ∃ next, app.handle (app.submit execution.application owner submission)
    ⟨(owner, execution.network.nextSerial owner), submission.emit
      (app.submit execution.application owner submission) owner (execution.network.known owner)⟩ =
        some next
  rw [emitted, unchanged, reactiveApplication_handle_of_tokenValid runtime leaks _ _
    (WitnessedPacket.tokenValid_opening _ _ _ _)]
  exact ⟨_, runtime.handle_opening_eq execution.application _ event candidate owner payload binding
    checks outputEq codeEq node ((execution.application.publicView_eventReady event).mp ready)
    timely rfl owned associated value valid stored (.success value) resolved⟩

/-- A permitted effective raw submission is precisely a successful compiled
disclosure. Guard failure and unusable private bindings are not silently
identified with this branch. Their attempted certificates fail the checker. -/
theorem service_opening_response [Fintype Player] (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (sound : (runtime.packetEvidence leaks).Sound execution)
    (invariant : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (submission : WitnessedSubmission graph)
    (named : (submission.emit ((runtime.reactiveApplication leaks).submit execution.application
      owner submission) owner (execution.network.known owner)).call.event? graph = some event)
    (available : (⟨some (.submit submission)⟩ : (runtime.reactiveApplication leaks).Action) ∈
      (bounds.menu runtime leaks).actions owner (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner))
    (permitted : runtime.freshServiceEnvelope execution.application.publicView
      ⟨(owner, execution.network.nextSerial owner), submission.emit
        ((runtime.reactiveApplication leaks).submit execution.application owner submission)
          owner (execution.network.known owner)⟩) :
    ∃ value, binding.get? execution.application.config.store = some (.success value) ∧
      EventCode.resolveOutput? binding checks true execution.application.config.store =
        some (.success value) ∧
      (⟨some (.submit submission)⟩ : (runtime.reactiveApplication leaks).Action) =
        runtime.serviceDecision leaks owner (execution.recall owner)
          (execution.observe (runtime.reactiveApplication leaks) owner) event
            (cast (congrArg EventField.Action outputEq.symm) true) := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨next, accepted⟩ := runtime.service_opening_accepted leaks execution owner sound
    invariant event payload binding checks outputEq codeEq node submission named permitted
  obtain ⟨candidate, raw, _, owned, associated, _, emitted, guards⟩ :=
    runtime.freshServiceEnvelope_resolution_shape execution.application.publicView owner event
      payload binding checks outputEq codeEq node _ named permitted
  change submission.emit (app.submit execution.application owner submission) owner
    (execution.network.known owner) =
      ⟨.opening event candidate raw, some ⟨candidate, raw⟩, some ⟨event⟩⟩ at emitted
  change execution.application.publicView.openingGuardsAccepted
    (submission.emit (app.submit execution.application owner submission) owner
      (execution.network.known owner)) = true at guards
  have addressed : submission.call.packet.event? graph = some event := named
  have certified : certifiedOpening (submission.emit
      (app.submit execution.application owner submission) owner (execution.network.known owner)) =
        true := by rw [emitted]; simp only [certifiedOpening, decide_true]
  obtain ⟨candidate, value, associated, owned, stored, resolved, normalized⟩ :=
    runtime.accepted_guarded_opening_normalization leaks execution.application next owner event
      payload binding checks outputEq codeEq node (execution.network.known owner) submission
        (execution.network.nextSerial owner) addressed certified guards accepted
  have known := app.known_from_recall execution owner recalled
  change execution.network.known owner = ReactiveApplication.ResponseMenu.knownPackets
    (execution.recall owner) (execution.observe app owner) at known
  have normal : submission.normalizeReactive owner (app.observePlayer execution.application owner)
      (execution.network.known owner) = submission := by
    have equal := ((bounds.menu_mem runtime leaks owner _ _ _).mp available).2
    change (⟨some (.submit (submission.normalizeReactive owner _ _))⟩ : app.Action) =
      ⟨some (.submit submission)⟩ at equal
    have fixed := ReactiveApplication.Transmission.submit.inj
      (Option.some.inj (congrArg ReactiveApplication.Action.transmission equal))
    rw [← known] at fixed
    exact fixed
  have call : submission.call.packet = .opening event candidate ⟨payload, value⟩ := by
    exact congrArg (fun material : WitnessedSubmission graph => material.call.packet)
      (normal.symm.trans normalized)
  have unchanged : app.submit execution.application owner submission = execution.application := by
    rcases submission with ⟨⟨packet, material⟩, request⟩
    dsimp only at call
    subst packet
    cases material <;> rfl
  have handled := reactiveHandle_call accepted
  change runtime.handle (app.submit execution.application owner submission)
    ⟨(owner, execution.network.nextSerial owner), submission.call.packet⟩ = some next at handled
  rw [unchanged, call] at handled
  have fixed := runtime.handle_opening_verified execution.application next
    (owner, execution.network.nextSerial owner) event candidate ⟨payload, value⟩ handled
  refine ⟨value, stored, resolved, ?_⟩
  rw [runtime.serviceDecision_successful_opening leaks execution recalled owner event payload
    binding checks outputEq codeEq node candidate value associated owned fixed resolved]
  exact congrArg (fun material => (⟨some (.submit material)⟩ : app.Action))
    (normal.symm.trans normalized)

/-- Once the original binding has failed, no effective fresh submission can
pass the public checker while its disclosure event is the owner's only ready
event, as a public resolution always is under the barrier order. Waiting and known-envelope
replay are still available; the hidden failure itself is not charged. -/
theorem failed_binding_submission_forbidden [Fintype Player] (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (sound : (runtime.packetEvidence leaks).Sound execution)
    (invariant : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (unique : ∀ other, execution.application.publicView.EventReady other →
      graph.actor? other = some owner → other = event)
    (failed : binding.get? execution.application.config.store = some .failure)
    (submission : WitnessedSubmission graph)
    (available : (⟨some (.submit submission)⟩ : (runtime.reactiveApplication leaks).Action) ∈
      (bounds.menu runtime leaks).actions owner (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner)) :
    runtime.permittedServiceEnvelope execution.application.publicView execution.network.ledger
      ⟨(owner, execution.network.nextSerial owner), submission.emit
        ((runtime.reactiveApplication leaks).submit execution.application owner submission)
          owner (execution.network.known owner)⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro allowed
  have permitted := (runtime.permittedServiceEnvelope_unpublished_iff _ _ _
    (serials.next_unpublished owner)).mp allowed
  obtain ⟨value, stored, _, _⟩ := runtime.service_opening_response leaks bounds execution owner
    sound invariant recalled event payload binding checks outputEq codeEq node submission
      (runtime.freshServiceEnvelope_event_of_owned_unique _ event _ unique permitted.2)
      available permitted.2
  rw [failed] at stored
  cases stored

end Vegas.EventGraphRuntime
