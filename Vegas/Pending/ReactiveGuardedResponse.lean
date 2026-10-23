/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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
      ⟨some ((disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
          owner
          (app.observePlayer execution.application owner) (execution.network.known owner))⟩ := by
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
  simp only [serviceDecision, view, reactiveDecision, node, packet, Option.map_some, normalized]
  change (⟨some ((disclosureSubmission (.opening event candidate
      ⟨payload, value⟩)).normalizeReactive
          owner
      (app.observePlayer execution.application owner)
      (ReactiveApplication.ResponseMenu.knownPackets (execution.recall owner)
        (execution.observe app owner)))⟩ : app.Action) = _
  rw [← known]

end Vegas.EventGraphRuntime
