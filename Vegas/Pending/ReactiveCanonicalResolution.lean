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

end Vegas.EventGraphRuntime
