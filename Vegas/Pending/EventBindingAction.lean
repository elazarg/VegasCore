/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventFreshCandidates
import Vegas.Pending.EventPlayerAction

/-! # Direct binding submissions

A fresh handle realizes any typed binding result in one player action,
regardless of occupied canonical slots. Inclusion remains a separate network
action. These are local construction laws, not a complete graph-policy compiler.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The same public packet represents a value or forfeiture. Its optional
opening data stays private and is registered as part of submission. -/
def bindingAction (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) : PlayerAction graph where
  memory := []
  transmission := some (.submit
    ⟨.commitment event (who, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩)

/-- The candidate has exactly the requested typed meaning before any delivery
or inclusion. No remembered-action or history premise is needed. -/
theorem bindingAction_result (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : NativeExecution runtime)
    (fresh : execution.native.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let next := runtime.takeAction who execution (bindingAction who event payload result serial)
    next.native.application.bindingResult (who, .prepared serial) payload = result := by
  cases result with
  | failure =>
      change (submitStep execution.native.application who
        (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, fresh]
  | success value =>
      simp only [takeAction, bindingAction, transmit, Submission.register, ↓reduceIte]
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, CommitmentCandidates.lookup_prepare_self,
        fresh, Raw.as?_mk, Option.elim_some]

/-- Binding material does not complete an event, overwrite recall, consume
clock time, or change the application's public projection. -/
theorem bindingAction_application (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : NativeExecution runtime) :
    let next := runtime.takeAction who execution (bindingAction who event payload result serial)
    next.native.application.config = execution.native.application.config ∧
      next.native.application.remembered = execution.native.application.remembered ∧
      next.native.application.publicView = execution.native.application.publicView := by
  exact runtime.transmit_application who execution.native
    (bindingAction who event payload result serial).transmission

/-- If the packet is included while the event is ready and timely, the actual
handler realizes precisely the requested graph action. Earlier cache entries
are irrelevant. This is an acceptance law, not an inclusion guarantee. -/
theorem bindingAction_handle (runtime : EventGraphRuntime graph) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (execution : NativeExecution runtime)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (fresh : execution.native.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : execution.native.application.accepted (.inr event) = none)
    (unused : execution.native.application.HandleUnused (owner, .prepared serial)) :
    let next := runtime.takeAction owner execution (bindingAction owner event payload result serial)
    (handle runtime next.native.application
      ⟨(owner, nonce), .commitment event (owner, .prepared serial)⟩).map State.config =
        some (execution.native.application.config.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) result)
          (cast (congrArg EventField.Value outputEq.symm) result)) := by
  let next := runtime.takeAction owner execution (bindingAction owner event payload result serial)
  have facts := runtime.bindingAction_application owner event payload result serial execution
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
  have selected := runtime.bindingAction_result owner event payload result serial execution fresh
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
theorem bindingAction_available (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (lower : Nat)
    (execution : NativeExecution runtime)
    (fresh : execution.native.application.FreshCandidates) :
    ∃ serial, lower ≤ serial ∧
      execution.native.application.HandleUnused (who, .prepared serial) ∧
      ∀ result : PublicationResult (L.Val payload),
        (runtime.actionStep who execution
          (bindingAction who event payload result serial)).map
            (fun next => next.native.application.bindingResult (who, .prepared serial) payload) =
          FinDist.pure result := by
  obtain ⟨serial, beyond, candidate, unused⟩ := fresh.exists_prepared who lower
  refine ⟨serial, beyond, unused, fun result => ?_⟩
  rw [actionStep, FinDist.map_pure,
    runtime.bindingAction_result who event payload result serial execution candidate]

end Vegas.EventGraphRuntime
