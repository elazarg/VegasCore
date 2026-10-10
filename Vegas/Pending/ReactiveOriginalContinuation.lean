/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOriginalConfig

/-! # Canonical continuation after an actual sampled original decision -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Evaluate the semantic continuation of a retained original decision. A
missing or unready intention leaves the continuation unchanged. -/
def originalDecisionContinuation (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (intention : Option graph.Completion) : PMF graph.SemanticKey :=
  match intention with
  | none => graph.canonicalContinuation profile config
  | some remembered =>
      if ready : config.cut.Ready remembered.event then
        (config.step remembered.event ready remembered.action).bind
          (graph.canonicalContinuation profile)
      else graph.canonicalContinuation profile config

/-- Sampling one actual original intention leaves the canonical semantic
continuation law unchanged. This is a decision-level equality; application
rounds still require protected settlement and preservation of the shadow state. -/
theorem prescribedReactiveResponse_canonicalContinuation
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion))
    (profile : graph.BehavioralProfile) (independent : graph.ReadyIndependent profile)
    (who : Player) (event : graph.EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (fresh : runtime.reactiveAlreadySubmitted leaks (execution.recall who) event = false)
    (undecided : runtime.reactiveAlreadyDecided leaks who (execution.recall who)
      (memories who) event = false)
    (actor : graph.actor? event = some who) :
    (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
      (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).bind
      (fun response => originalDecisionContinuation graph profile
        (runtime.originalConfig leaks execution memories) response.2) =
      graph.canonicalContinuation profile (runtime.originalConfig leaks execution memories) := by
  have ready : (runtime.originalConfig leaks execution memories).cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (execution.application.publicView.ownTurn?_spec who event turn).1
  rw [runtime.prescribedReactiveResponse_originalConfig leaks execution memories who
    (profile who) event turn fresh undecided actor, PMF.bind_map]
  simp only [Function.comp_def, originalDecisionContinuation, dite_eq_left ready]
  rw [← PMF.bind_bind]
  have continuation := independent.normalizedThenCanonical_eq
    (runtime.originalConfig leaks execution memories) event ready
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
