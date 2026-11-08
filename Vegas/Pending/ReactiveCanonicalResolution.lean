/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Pending.ReactiveCompiledResolution

/-! # Canonical resolution responses

Withholding is silent. A requested disclosure transmits an authentic opening
when the stored binding succeeds and its accepted handle belongs to the sender.
Missing, failed or nonowned opening material produces silence. Public guard
rejection is evaluated after transmission by the handler.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
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
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq) :
    (canonicalServiceDecision timeouts) leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) false) = ⟨none⟩ := by
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · exact (canonicalServiceDecision_defaulted timeouts) leaks who past view event _ inactive
  · rw [(canonicalServiceDecision_eq_of_not_bind timeouts) leaks who past view event _
      (resolve_not_bind node)]
    simp only [serviceDecision, reactiveDecision, ite_eq_right inactive, node,
      reactiveResolutionPacket, cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
      Option.map_none]
    rfl

/-- A requested canonical disclosure is silent when no stored successful binding
has an accepted handle owned by the sender. -/
theorem canonicalServiceDecision_resolution_unavailable
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (failed : ∀ value candidate,
      binding.get? view.application.observation.store = some (.success value) →
        view.application.publicView.accepted binding.field = some candidate →
          candidate.1 ≠ who) :
    (canonicalServiceDecision timeouts) leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) true) = ⟨none⟩ := by
  rw [(canonicalServiceDecision_eq_of_not_bind timeouts) leaks who past view event _
    (resolve_not_bind node)]
  rcases (serviceDecision_resolution_cases timeouts) leaks who past view event actor payload
    binding checks outputEq codeEq node true with
      silent | ⟨candidate, value, _, resolved, associated, owned, _⟩
  · exact silent
  · exact (failed value candidate resolved associated owned).elim

end Vegas.EventGraphRuntime
