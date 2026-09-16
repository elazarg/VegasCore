/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SequentialLaw
import Vegas.EventGraph.Semantics

/-! # EventGraph execution modes

Execution modes select dependency constraints on one graph representation.
Concurrent mode retains the graph's declared dependencies. Sequential mode
adds every source-earlier event as a predecessor. Fields, node code, actions,
inputs, and payoffs are retained. Graph-indexed completion records,
observations, and policies have explicit lossless transports between modes.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type}
variable {L : IExpr} [IExpr.ResultTypes L]

variable [DecidableEq Player]

omit [DecidableEq Player] in
@[simp] theorem fromModePolicy_toModePolicy
    (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (who : Player) (policy : graph.BehavioralPolicy who) :
    graph.fromModePolicy mode who (graph.toModePolicy mode who policy) = policy := by
  funext event actor observation
  simp [toModePolicy, fromModePolicy]

omit [DecidableEq Player] in
@[simp] theorem toModePolicy_fromModePolicy
    (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (who : Player) (policy : (graph.withMode mode).BehavioralPolicy who) :
    graph.toModePolicy mode who (graph.fromModePolicy mode who policy) = policy := by
  funext event actor observation
  simp [toModePolicy, fromModePolicy]

omit [DecidableEq Player] in
@[simp] theorem fromModeProfile_toModeProfile
    (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (profile : graph.BehavioralProfile) :
    graph.fromModeProfile mode (graph.toModeProfile mode profile) = profile := by
  funext who
  exact graph.fromModePolicy_toModePolicy mode who (profile who)

omit [DecidableEq Player] in
@[simp] theorem toModeProfile_fromModeProfile
    (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (profile : (graph.withMode mode).BehavioralProfile) :
    graph.toModeProfile mode (graph.fromModeProfile mode profile) = profile := by
  funext who
  exact graph.toModePolicy_fromModePolicy mode who (profile who)

/-- Transporting a unilateral profile update into a mode transports exactly
the replacement policy and leaves every opponent unchanged. -/
theorem toModeProfile_update (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) (profile : graph.BehavioralProfile)
    (who : Player) (replacement : graph.BehavioralPolicy who) :
    graph.toModeProfile mode
        (GameTheory.Profile.update (sig := graph.gameSignature)
          profile who replacement) =
      GameTheory.Profile.update (sig := (graph.withMode mode).gameSignature)
        (graph.toModeProfile mode profile) who
          (graph.toModePolicy mode who replacement) := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [toModeProfile, GameTheory.Profile.update_same]
  · simp only [toModeProfile, GameTheory.Profile.update_of_ne _ _ same]

/-- Forgetting a mode after a unilateral profile update forgets exactly the
replacement policy and leaves every opponent unchanged. -/
theorem fromModeProfile_update (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode)
    (profile : (graph.withMode mode).BehavioralProfile)
    (who : Player)
    (replacement : (graph.withMode mode).BehavioralPolicy who) :
    graph.fromModeProfile mode
        (GameTheory.Profile.update (sig := (graph.withMode mode).gameSignature)
          profile who replacement) =
      GameTheory.Profile.update (sig := graph.gameSignature)
        (graph.fromModeProfile mode profile) who
          (graph.fromModePolicy mode who replacement) := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [fromModeProfile, GameTheory.Profile.update_same]
  · simp only [fromModeProfile, GameTheory.Profile.update_of_ne _ _ same]

omit [DecidableEq Player] in
@[simp] theorem toModeObservation_concurrent
    (graph : Vegas.EventGraph Player L) (who : Player)
    (observation : graph.PlayerObservation who) :
    graph.toModeObservation .concurrent who observation = observation := by
  apply PlayerObservation.ext graph
  · rfl
  · rfl
  · simp only [toModeObservation]
    induction observation.ownActions with
    | nil => rfl
    | cons completion rest ih =>
        cases completion
        simp [toModeCompletion, ih]

omit [DecidableEq Player] in
@[simp] theorem fromModeProfile_concurrent
    (graph : Vegas.EventGraph Player L)
    (profile : (graph.withMode .concurrent).BehavioralProfile) :
    graph.fromModeProfile .concurrent profile = profile := by
  funext who event actor observation
  simp [fromModeProfile, fromModePolicy]

/-- Canonical execution has the same typed terminal-store law in either
dependency mode after forgetting the mode from the behavioral profile. -/
theorem runPolicies_withMode_store (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode)
    (profile : (graph.withMode mode).BehavioralProfile)
    (inputs : graph.Inputs) :
    ((graph.withMode mode).runPolicies
      (graph.withMode mode).canonicalScheduler profile inputs).map Config.store =
    (graph.runPolicies graph.canonicalScheduler
      (graph.fromModeProfile mode profile) inputs).map Config.store := by
  cases mode with
  | concurrent =>
      cases graph
      simp [withMode]
  | sequential =>
      simpa using graph.canonical_fromSequential_store_law profile inputs

end Vegas.EventGraph
