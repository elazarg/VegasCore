/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveGuardConformance
import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveDisclosure

/-! # Guarded opening classification in the full-source retained menu

Successful public guard checks identify an actual retained source disclosure.
The test keeps arbitrary hidden values and deferred guards. Own recall enforces
the separate once-per-event rule; authentic phase records must establish that
rule when an external auditor uses this classification.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The actual successful compiler response is the unique semantic normal form
of its matching certificate, including forwarding aliases. -/
theorem serviceDecision_successful_opening
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (value : L.Val payload)
    (associated : execution.application.accepted binding.field = some candidate)
    (owned : candidate.1 = owner)
    (fixed : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (resolved : EventCode.resolveOutput? binding checks true execution.application.config.store =
      some (.success value)) :
    let app := runtime.reactiveApplication leaks
    runtime.serviceDecision leaks owner (execution.recall owner) (execution.observe app owner)
      event (cast (congrArg EventField.Action outputEq.symm) true) =
      ⟨some (.submit
        ((disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive owner
          (app.observePlayer execution.application owner) (execution.network.known owner)))⟩ := by
  intro app
  have localResult : EventCode.resolveOutput? binding checks true
      (app.observePlayer execution.application owner).observation.store =
      some (.success value) := by
    change EventCode.resolveOutput? binding checks true
      (graph.playerStore owner execution.application.config.store) = _
    rw [EventCode.resolveOutput?_playerStore]
    exact resolved
  have packet := reactiveResolutionPacket_opening owner event payload binding checks outputEq
    (cast (congrArg EventField.Action outputEq.symm) true)
    (app.observePlayer execution.application owner) (by simp only [cast_cast, cast_eq]) value
    localResult candidate associated owned
  have localFixed : (app.observePlayer execution.application owner).candidates candidate.2 =
      .openable ⟨payload, value⟩ := by
    change execution.application.candidates.lookup (owner, candidate.2) = _
    simpa only [← owned, Prod.mk.eta] using fixed
  have normalized := disclosureSubmission_normalize_opening owner
    (app.observePlayer execution.application owner) event candidate ⟨payload, value⟩
      owned localFixed
  have known := app.known_from_recall execution owner recalled
  change execution.network.known owner = ReactiveApplication.ResponseMenu.knownPackets
    (execution.recall owner) (execution.observe app owner) at known
  have view : (execution.observe app owner).application =
      app.observePlayer execution.application owner := rfl
  simp only [serviceDecision, view, reactiveDecision, node, packet, normalized]
  change (⟨some (.submit
    ((disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive owner
      (app.observePlayer execution.application owner)
      (ReactiveApplication.ResponseMenu.knownPackets (execution.recall owner)
        (execution.observe app owner))))⟩ : app.Action) = _
  rw [← known]

/-- A first effective current opening passing the public checks is an actual
retained choice. Private evidence names and registration fields add no case. -/
theorem guarded_submission_retained [Fintype Player] (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (actor : graph.actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (submission : WitnessedSubmission graph)
    (available : (⟨some (.submit submission)⟩ : (runtime.reactiveApplication leaks).Action) ∈
      (bounds.menu runtime leaks).actions owner (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner))
    (first : runtime.firstSubmission leaks (execution.recall owner)
      ⟨some (.submit submission)⟩ = true)
    (addressed : submission.call.packet.event? graph = some event)
    (serial : Nat) (next : State graph)
    (certified : certifiedOpening (submission.emit
      ((runtime.reactiveApplication leaks).submit execution.application owner submission)
        owner (execution.network.known owner)) = true)
    (guards : execution.application.publicView.openingGuardsAccepted (submission.emit
      ((runtime.reactiveApplication leaks).submit execution.application owner submission)
        owner (execution.network.known owner)) = true)
    (accepted : (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit execution.application owner submission)
      ⟨(owner, serial), submission.emit
        ((runtime.reactiveApplication leaks).submit execution.application owner submission)
          owner (execution.network.known owner)⟩ = some next) :
    (⟨some (.submit submission)⟩ : (runtime.reactiveApplication leaks).Action) ∈
      bounds.compiledActions runtime leaks owner (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner) := by
  classical
  let app := runtime.reactiveApplication leaks
  obtain ⟨candidate, value, associated, owned, stored, resolved, normalized⟩ :=
    runtime.accepted_guarded_opening_normalization leaks execution.application next owner event
      payload binding checks outputEq codeEq node (execution.network.known owner) submission serial
      addressed certified guards accepted
  have known := app.known_from_recall execution owner recalled
  change execution.network.known owner = ReactiveApplication.ResponseMenu.knownPackets
    (execution.recall owner) (execution.observe app owner) at known
  have normal : submission.normalizeReactive owner (app.observePlayer execution.application owner)
      (execution.network.known owner) = submission := by
    have invariant := ((bounds.menu_mem runtime leaks owner (execution.recall owner)
      (execution.observe app owner) _).mp available).2
    change (⟨some (.submit (submission.normalizeReactive owner _ _))⟩ : app.Action) =
      ⟨some (.submit submission)⟩ at invariant
    have same := ReactiveApplication.Transmission.submit.inj
      (Option.some.inj (congrArg ReactiveApplication.Action.transmission invariant))
    rw [← known] at same
    exact same
  have originalCall : submission.call.packet = .opening event candidate ⟨payload, value⟩ := by
    have same := congrArg (fun material : WitnessedSubmission graph => material.call.packet)
      (normal.symm.trans normalized)
    exact same
  have unchanged : app.submit execution.application owner submission = execution.application := by
    rcases submission with ⟨⟨packet, material⟩, evidence⟩
    dsimp only at originalCall
    subst packet
    cases material <;> rfl
  have fixed : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ := by
    have applied := accepted
    change handle runtime (app.submit execution.application owner submission)
      ⟨(owner, serial), submission.call.packet⟩ = some next at applied
    rw [unchanged, originalCall] at applied
    exact runtime.handle_opening_verified execution.application next (owner, serial) event
      candidate ⟨payload, value⟩ applied
  have response : (⟨some (.submit submission)⟩ : app.Action) =
      runtime.serviceDecision leaks owner (execution.recall owner) (execution.observe app owner)
        event (cast (congrArg EventField.Action outputEq.symm) true) := by
    rw [runtime.serviceDecision_successful_opening leaks execution recalled owner event payload
      binding checks outputEq codeEq node candidate value associated owned fixed resolved]
    exact congrArg (fun material => (⟨some (.submit material)⟩ : app.Action))
      (normal.symm.trans normalized)
  apply bounds.decision_compiled runtime leaks owner (execution.recall owner)
    (execution.observe app owner) ⟨some (.submit submission)⟩ _ first available
  rw [response]
  have publicReady := (execution.application.publicView_eventReady event).mpr ready
  have grantedView : (execution.observe app owner).application.publicView.serviceGrant =
      some event := granted
  have readyView : (execution.observe app owner).application.publicView.EventReady event :=
    publicReady
  simp only [MessageBounds.decisionActions, grantedView, actor, readyView, and_self, ↓reduceIte,
    node]
  exact Finset.mem_image.mpr ⟨true, Finset.mem_univ _, rfl⟩

end Vegas.EventGraphRuntime
