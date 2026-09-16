/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.MemoizedPolicy
import Vegas.Pending.EventPolicyBlock

/-! # A continuation law for native remembered actions

The potential uses only the runtime's graph configuration and existing choice
cache. It fixes already sampled actions in the graph continuation; it does not
introduce another execution state. The local sampling equation below is not
yet a whole-service honest law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Canonical future semantic law with the native cache's sampled actions
fixed. Completed cache entries are harmless by graph-policy irrelevance. -/
def State.continuationLaw (state : State graph) (profile : graph.BehavioralProfile) :
    FinDist graph.SemanticKey :=
  graph.canonicalContinuation (graph.memoizedProfile profile state.remembered) state.config

/-- At terminal execution the continuation is exactly the native semantic
state, independently of all retained cache entries. -/
theorem State.continuationLaw_terminal (state : State graph)
    (profile : graph.BehavioralProfile) (terminal : state.config.cut.Terminal) :
    state.continuationLaw profile = FinDist.pure (graph.semanticKey state.config) :=
  (graph.canonicalContinuation_terminal _ state.config terminal).symm

/-- The actual private sampling command preserves the continuation law in
expectation. No scheduler factorization or extra ideal execution is assumed. -/
theorem playerStep_remember_continuation (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (execution : runtime.application.PolicyExecution) (event : graph.EventId)
    (ready : execution.native.application.config.cut.Ready event) (who : Player)
    (actor : graph.actor? event = some who)
    (empty : execution.native.application.remembered event = none) :
    ((graph.normalizePolicy who (profile who) event actor
      (graph.playerObserve who execution.native.application.config)).bind fun action =>
        (runtime.application.playerStep who execution
          (.privateCommand (.remember event action))).bind
          fun next => next.native.application.continuationLaw profile) =
      execution.native.application.continuationLaw profile := by
  simp only [runtime.application.playerStep_private_eq, FinDist.pure_bind]
  change ((graph.normalizePolicy who (profile who) event actor
    (graph.playerObserve who execution.native.application.config)).bind fun action =>
      (privateStep execution.native.application who (.remember event action)).continuationLaw
        profile) = _
  simp only [privateStep, dif_pos actor, empty, State.continuationLaw]
  exact (ordered.canonicalContinuation_remember profile
    execution.native.application.remembered execution.native.application.config
    event ready who actor empty).symm

end Vegas.EventGraphRuntime
