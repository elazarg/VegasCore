/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Pending.ReactiveOpeningWindow
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.EventGraph.ResolutionProvenance

/-! # Canonical resolution responses

At a resolution the canonical decision is silent unless the owner discloses
and owner-local validation succeeds: the owner's view of the store makes the
resolution publish a value, and the binding's accepted handle is the owner's.
In that case it sends the opening of that handle with the value, and the
emitted packet carries the authentic opening certificate of the handle. Source
FALSE is therefore implemented by silence until expiry, and TRUE whose
validation fails is silent as well.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

omit [DecidableEq Player] in
private theorem resolve_not_bind {event : graph.EventId} {actor : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding actor payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks}
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq) :
    ∀ owner payload outputEq codeEq,
      nodeView graph event ≠ .bind owner payload outputEq codeEq := by
  intro owner other bindEq bindCode same
  rw [node] at same
  cases same

/-- **Canonical FALSE is silence.** -/
theorem canonicalServiceDecision_resolution_false
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq) :
    runtime.canonicalServiceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) false) = ⟨none⟩ := by
  rw [runtime.canonicalServiceDecision_eq_of_not_bind leaks who past view event _
    (resolve_not_bind node)]
  simp only [serviceDecision, reactiveDecision, node, reactiveResolutionPacket, cast_cast,
    cast_eq, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  rfl

/-- **Canonical TRUE without successful owner-local validation is silence.**
Validation fails when the owner's view of the store does not make the
resolution publish a value, or the binding's accepted handle is missing or
not the owner's. -/
theorem canonicalServiceDecision_resolution_unvalidated
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (failed : ∀ value candidate,
      EventCode.resolveOutput? binding checks true view.application.observation.store =
          some (.success value) →
        view.application.publicView.accepted binding.field = some candidate →
          candidate.1 ≠ who) :
    runtime.canonicalServiceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) true) = ⟨none⟩ := by
  rw [runtime.canonicalServiceDecision_eq_of_not_bind leaks who past view event _
    (resolve_not_bind node)]
  rcases runtime.serviceDecision_resolution_cases leaks who past view event actor payload
    binding checks outputEq codeEq node true with
      silent | ⟨candidate, value, _, resolved, associated, owned, _⟩
  · exact silent
  · exact (failed value candidate resolved associated owned).elim

/-- **Canonical TRUE with successful owner-local validation sends the
authentic opening.** At every execution satisfying the binding invariant and
input recall, when the owner's view of the store makes the resolution publish
`value` and the binding's accepted handle is the owner's, the canonical TRUE
response transmits one submission, and the packet it emits is the opening of
that handle with `value`, carrying the handle's authentic opening certificate
and the readiness token of the owner's current view. -/
theorem canonicalServiceDecision_resolution_validated
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (valid : execution.application.BindingInvariant)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (value : L.Val payload)
    (validated : EventCode.resolveOutput? binding checks true
      ((execution.observe (runtime.reactiveApplication leaks) owner).application.observation.store)
        = some (.success value))
    (associated : execution.application.accepted binding.field = some candidate)
    (owned : candidate.1 = owner) :
    let app := runtime.reactiveApplication leaks
    ∃ material, runtime.canonicalServiceDecision leaks owner (execution.recall owner)
        (execution.observe app owner) event
        (cast (congrArg EventField.Action outputEq.symm) true) = ⟨some material⟩ ∧
      app.packet (app.submit execution.application owner material) owner
          (execution.network.known owner) material =
        ⟨.opening event candidate ⟨payload, value⟩, some ⟨candidate, ⟨payload, value⟩⟩,
          execution.application.publicView.tokenFor
            (.opening event candidate ⟨payload, value⟩)⟩ := by
  intro app
  have resolved : EventCode.resolveOutput? binding checks true
      execution.application.config.store = some (.success value) := by
    change EventCode.resolveOutput? binding checks true
      (graph.playerStore owner execution.application.config.store) = _ at validated
    rwa [EventCode.resolveOutput?_playerStore] at validated
  have stored := EventCode.binding_success_of_resolve_success binding checks true
    execution.application.config.store value resolved
  obtain ⟨actual, accepted, _, fixed⟩ := valid.success_provenance binding value stored
  cases Option.some.inj (accepted.symm.trans associated)
  let material := (disclosureSubmission (.opening event candidate ⟨payload, value⟩)
    ).normalizeReactive owner (app.observePlayer execution.application owner)
      (execution.network.known owner)
  refine ⟨material, ?_, ?_⟩
  · rw [runtime.canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _
      (resolve_not_bind node)]
    exact runtime.serviceDecision_successful_opening leaks execution recalled owner event
      payload binding checks outputEq codeEq node candidate value associated owned fixed resolved
  · have sameSubmit := (runtime.reactiveNormalization leaks).submit execution.application
      owner (execution.network.known owner)
        (disclosureSubmission (.opening event candidate ⟨payload, value⟩))
    dsimp only [reactiveNormalization] at sameSubmit
    change app.packet (app.submit execution.application owner material) owner
      (execution.network.known owner) material = _
    change app.submit execution.application owner material =
      app.submit execution.application owner _ at sameSubmit
    rw [sameSubmit]
    exact (WitnessedSubmission.normalizeReactive_emit runtime leaks execution.application owner
      (execution.network.known owner)
        (disclosureSubmission (.opening event candidate ⟨payload, value⟩))).trans
      (runtime.windowOpening_packet leaks owner event candidate ⟨payload, value⟩
        execution.application (execution.network.known owner) owned fixed)

/-- The authentic-opening clause at every legal initialized history, under
arbitrary player responses and every scheduler. -/
theorem history_canonicalServiceDecision_resolution_validated
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (value : L.Val payload)
    (validated : EventCode.resolveOutput? binding checks true
      ((control.execution.observe (runtime.reactiveApplication leaks)
        owner).application.observation.store) = some (.success value))
    (associated : control.execution.application.accepted binding.field = some candidate)
    (owned : candidate.1 = owner) :
    let app := runtime.reactiveApplication leaks
    ∃ material, runtime.canonicalServiceDecision leaks owner (control.execution.recall owner)
        (control.execution.observe app owner) event
        (cast (congrArg EventField.Action outputEq.symm) true) = ⟨some material⟩ ∧
      app.packet (app.submit control.execution.application owner material) owner
          (control.execution.network.known owner) material =
        ⟨.opening event candidate ⟨payload, value⟩, some ⟨candidate, ⟨payload, value⟩⟩,
          control.execution.application.publicView.tokenFor
            (.opening event candidate ⟨payload, value⟩)⟩ :=
  runtime.canonicalServiceDecision_resolution_validated leaks control.execution
    ((runtime.reactiveApplication leaks).history_inputRecall (inputs.map State.initial) horizon
      scheduler trace)
    (runtime.reactiveBindingInvariant_history leaks inputs horizon scheduler trace)
    owner event payload binding checks outputEq codeEq node candidate value validated associated
    owned

end Vegas.EventGraphRuntime
