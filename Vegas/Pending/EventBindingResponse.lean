/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventFreshCandidates
import Interaction.MessageApplicationResponse

/-! # Binding material within one response

A fresh handle realizes any typed binding result in one response, regardless
of earlier remembered actions or occupied canonical slots. Private preparation
and public submission are atomic; inclusion remains a later network action.
These are local construction laws, not a complete graph-policy compiler.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Both binding outcomes send the same envelope at the same invocation.
Failure leaves the fresh handle unprepared; submission permanently freezes it. -/
def bindingResponse (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) : runtime.application.PlayerResponse where
  privateWork := match result with
    | .failure => []
    | .success value => [.prepare serial ⟨payload, value⟩]
  network := .submit (.commitment event (who, .prepared serial))

def bindingResponseExecution (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : runtime.application.PolicyExecution) :
    runtime.application.PolicyExecution :=
  runtime.application.afterSubmit
    (runtime.application.afterPrivateWork who
      (runtime.bindingResponse who event payload result serial).privateWork execution)
    who (.commitment event (who, .prepared serial))

theorem bindingResponse_step (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : runtime.application.PolicyExecution) :
    runtime.application.responseStep who execution
        (runtime.bindingResponse who event payload result serial) =
      FinDist.pure (runtime.bindingResponseExecution who event payload result serial execution) :=
  runtime.application.responseStep_submit who execution _ _

/-- The candidate has exactly the requested typed meaning before any delivery
or inclusion. No remembered-action or history premise is needed. -/
theorem bindingResponse_result (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : runtime.application.PolicyExecution)
    (fresh : execution.native.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let next := runtime.bindingResponseExecution who event payload result serial execution
    next.native.application.bindingResult (who, .prepared serial) payload = result := by
  cases result with
  | failure =>
      change (submitStep execution.native.application who
        (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, fresh]
  | success value =>
      change (submitStep (privateStep execution.native.application who
        (.prepare serial ⟨payload, value⟩)) who
          (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, privateStep, CommitmentCandidates.lookup_prepare_self,
        fresh, Raw.as?_mk, Option.elim_some]

/-- Binding material does not complete an event, overwrite recall, consume
clock time, or change the application's public projection. -/
theorem bindingResponse_application (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : runtime.application.PolicyExecution) :
    let next := runtime.bindingResponseExecution who event payload result serial execution
    next.native.application.config = execution.native.application.config ∧
      next.native.application.remembered = execution.native.application.remembered ∧
      next.native.application.publicView = execution.native.application.publicView := by
  cases result <;> exact ⟨rfl, rfl, rfl⟩

/-- If the packet is included while the event is ready and timely, the actual
handler realizes precisely the requested graph action. Earlier cache entries
are irrelevant. This is an acceptance law, not an inclusion guarantee. -/
theorem bindingResponse_handle (runtime : EventGraphRuntime graph) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (execution : runtime.application.PolicyExecution)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (fresh : execution.native.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : execution.native.application.accepted (.inr event) = none)
    (unused : execution.native.application.HandleUnused (owner, .prepared serial)) :
    let next := runtime.bindingResponseExecution owner event payload result serial execution
    (handle runtime next.native.application
      ⟨(owner, nonce), .commitment event (owner, .prepared serial)⟩).map State.config =
        some (execution.native.application.config.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) result)
          (cast (congrArg EventField.Value outputEq.symm) result)) := by
  let next := runtime.bindingResponseExecution owner event payload result serial execution
  have facts := runtime.bindingResponse_application owner event payload result serial execution
  have configEq : next.native.application.config = execution.native.application.config := facts.1
  have publicEq : next.native.application.publicView = execution.native.application.publicView :=
    facts.2.2
  have acceptedEq : next.native.application.accepted = execution.native.application.accepted :=
    congrArg PublicView.accepted publicEq
  have nextReady : next.native.application.config.cut.Ready event := by
    simpa only [configEq] using ready
  have nextTimely : next.native.application.WithinDeadline runtime event := by
    have clockEq : next.native.application.clock = execution.native.application.clock :=
      congrArg PublicView.clock publicEq
    have activatedEq : next.native.application.activatedAt =
        execution.native.application.activatedAt := congrArg PublicView.activatedAt publicEq
    simpa only [State.WithinDeadline, clockEq, activatedEq] using timely
  have nextVacant : next.native.application.accepted (.inr event) = none := by
    simpa only [acceptedEq] using vacant
  have nextUnused : next.native.application.HandleUnused (owner, .prepared serial) := by
    simpa only [State.HandleUnused, acceptedEq] using unused
  have selected := runtime.bindingResponse_result owner event payload result serial execution fresh
  change (handle runtime next.native.application _).map State.config = _
  rw [runtime.handle_commitment_eq next.native.application (owner, nonce) event
    (owner, .prepared serial) owner payload outputEq codeEq viewNode nextReady nextTimely
    rfl rfl nextVacant nextUnused, Option.map_some]
  change some (next.native.application.config.complete event nextReady
    (cast (congrArg EventField.Action outputEq.symm) (next.native.application.bindingResult _ _))
    (cast (congrArg EventField.Value outputEq.symm)
      (next.native.application.bindingResult _ _))) = _
  change next.native.application.bindingResult _ _ = result at selected
  rw [selected]
  simp only [configEq]

/-- Fresh material remains available at arbitrarily large serials. The
quantifier over results is inside the slot witness: allocation need not inspect
the value or the decision to forfeit. -/
theorem bindingResponse_available (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (lower : Nat)
    (execution : runtime.application.PolicyExecution)
    (fresh : execution.native.application.FreshCandidates) :
    ∃ serial, lower ≤ serial ∧
      execution.native.application.HandleUnused (who, .prepared serial) ∧
      ∀ result : PublicationResult (L.Val payload),
        (runtime.application.responseStep who execution
          (runtime.bindingResponse who event payload result serial)).map
            (fun next => next.native.application.bindingResult (who, .prepared serial) payload) =
          FinDist.pure result := by
  obtain ⟨serial, beyond, candidate, unused⟩ := fresh.exists_prepared who lower
  refine ⟨serial, beyond, unused, fun result => ?_⟩
  rw [bindingResponse_step, FinDist.map_pure,
    runtime.bindingResponse_result who event payload result serial execution candidate]

end Vegas.EventGraphRuntime
