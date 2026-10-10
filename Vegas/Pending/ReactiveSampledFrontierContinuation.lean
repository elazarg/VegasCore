/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOriginalContinuation
import Vegas.EventGraph.ForeignCompletionSequence

/-! # Canonical potentials at sampled pending-event frontiers -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- An actual first decision preserves the canonical semantic continuation at
a frontier which has already completed supported pending decisions of other
owners. Conditioning on those pending packets does not cause resampling. -/
theorem prescribedReactiveResponse_sampledFrontierContinuation
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion))
    (who : Player)
    (profile : graph.BehavioralProfile) (ordered : graph.BarrierOrdered)
    (frontier : graph.Config)
    (pending : graph.ForeignCompletionSequence who
      (runtime.originalConfig leaks execution memories) frontier)
    (event : graph.EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (fresh : runtime.reactiveAlreadySubmitted leaks (execution.recall who) event = false)
    (undecided : runtime.reactiveAlreadyDecided leaks who (execution.recall who)
      (memories who) event = false)
    (actor : graph.actor? event = some who) :
    (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
      (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).bind
      (fun response => originalDecisionContinuation graph profile
        frontier response.2) =
      graph.canonicalContinuation profile frontier := by
  have ready : (runtime.originalConfig leaks execution memories).cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (execution.application.publicView.ownTurn?_spec who event turn).1
  have transported := pending.normalizePolicy_eq ordered (profile who) event ready actor
  rw [runtime.prescribedReactiveResponse_originalConfig leaks execution memories who
    (profile who) event turn fresh undecided actor]
  rw [← transported.2, PMF.bind_map]
  simp only [Function.comp_def, originalDecisionContinuation, dite_eq_left transported.1]
  rw [← PMF.bind_bind]
  have continuation := (ordered.readyIndependent profile).normalizedThenCanonical_eq
    frontier event transported.1
  unfold normalizedThenCanonical normalizedPolicyStep at continuation
  split at continuation
  · rename_i owner owned
    have same : owner = who := Option.some.inj (owned.symm.trans actor)
    subst owner
    exact continuation
  · rename_i unowned
    rw [actor] at unowned
    cases unowned

end Vegas.EventGraphRuntime
