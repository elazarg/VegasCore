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

/-- Dependency constraint used by an EventGraph execution. -/
inductive ExecutionMode where
  | concurrent
  | sequential
  deriving DecidableEq, Repr

variable {Player : Type}
variable {L : IExpr} [IExpr.ResultTypes L]

/-- Apply an execution mode by changing only the graph's dependency order. -/
def withMode (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) : Vegas.EventGraph Player L where
  inputCount := graph.inputCount
  order := {
    eventCount := graph.order.eventCount
    predecessors := fun event => match mode with
      | .concurrent => graph.order.predecessors event
      | .sequential => Finset.univ.filter fun prior => prior.val < event.val
    predecessor_lt := by
      intro event predecessor member
      cases mode with
      | concurrent => exact graph.order.predecessor_lt member
      | sequential => exact (Finset.mem_filter.mp member).2 }
  inputLayout := graph.inputLayout
  outputLayout := graph.outputLayout
  nodes := graph.nodes
  reads_available := by
    intro event field read
    cases mode with
    | concurrent => exact graph.reads_available event field read
    | sequential =>
        cases field with
        | inl => trivial
        | inr producer =>
            apply (EventOrder.sequential.mem_predecessors producer event).2
            exact graph.order.predecessor_lt
              (graph.reads_available event (.inr producer) read)
  payoffs := graph.payoffs

@[simp] theorem withMode_concurrent (graph : Vegas.EventGraph Player L) :
    graph.withMode .concurrent = graph := by
  cases graph
  simp only [withMode]

@[simp] theorem withMode_sequential (graph : Vegas.EventGraph Player L) :
    graph.withMode .sequential = graph.sequentialize := rfl

@[simp] theorem withMode_inputCount (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) :
    (graph.withMode mode).inputCount = graph.inputCount := rfl

@[simp] theorem withMode_eventCount (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) :
    (graph.withMode mode).order.eventCount = graph.order.eventCount := by
  cases mode <;> rfl

@[simp] theorem withMode_inputLayout (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) (input : graph.InputId) :
    (graph.withMode mode).inputLayout input = graph.inputLayout input := rfl

@[simp] theorem withMode_outputLayout (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) (event : graph.EventId) :
    (graph.withMode mode).outputLayout event = graph.outputLayout event := rfl

@[simp] theorem withMode_nodes (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) (event : graph.EventId) :
    (graph.withMode mode).nodes event = graph.nodes event := rfl

@[simp] theorem withMode_payoffs (graph : Vegas.EventGraph Player L)
    (mode : ExecutionMode) :
    (graph.withMode mode).payoffs = graph.payoffs := rfl

variable [DecidableEq Player]

/-- Required public barriers survive either dependency mode. -/
theorem withMode_barrierOrdered (graph : Vegas.EventGraph Player L)
    (ordered : graph.BarrierOrdered) (mode : ExecutionMode) :
    (graph.withMode mode).BarrierOrdered := by
  cases mode with
  | concurrent => simpa using ordered
  | sequential => simpa using graph.sequentialize_barrierOrdered

/-- Reinterpret one chronological completion under a dependency mode. -/
def toModeCompletion (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (completion : graph.Completion) : (graph.withMode mode).Completion where
  event := completion.event
  action := completion.action

/-- Forget the dependency mode from one chronological completion. -/
def fromModeCompletion (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (completion : (graph.withMode mode).Completion) : graph.Completion where
  event := completion.event
  action := completion.action

/-- Reinterpret a player observation under a dependency mode. -/
def toModeObservation (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (who : Player) (observation : graph.PlayerObservation who) :
    (graph.withMode mode).PlayerObservation who where
  completionOrder := observation.completionOrder
  store := observation.store
  ownActions := observation.ownActions.map (graph.toModeCompletion mode)

/-- Forget the dependency mode from a player observation. -/
def fromModeObservation (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (who : Player) (observation : (graph.withMode mode).PlayerObservation who) :
    graph.PlayerObservation who where
  completionOrder := observation.completionOrder
  store := observation.store
  ownActions := observation.ownActions.map (graph.fromModeCompletion mode)

/-- Reinterpret a policy on the mode-constrained graph. Policy inputs and
actions are unchanged because dependency cuts are not part of observations. -/
def toModePolicy (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (graph.withMode mode).BehavioralPolicy who :=
  fun event actor observation =>
    policy event actor (graph.fromModeObservation mode who observation)

/-- Forget a graph's dependency mode from a behavioral policy. -/
def fromModePolicy (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (who : Player) (policy : (graph.withMode mode).BehavioralPolicy who) :
    graph.BehavioralPolicy who :=
  fun event actor observation =>
    policy event actor (graph.toModeObservation mode who observation)

/-- Reinterpret a complete behavioral profile on a dependency mode. -/
def toModeProfile (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (profile : graph.BehavioralProfile) :
    (graph.withMode mode).BehavioralProfile :=
  fun who => graph.toModePolicy mode who (profile who)

/-- Forget a dependency mode from a complete behavioral profile. -/
def fromModeProfile (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (profile : (graph.withMode mode).BehavioralProfile) :
    graph.BehavioralProfile :=
  fun who => graph.fromModePolicy mode who (profile who)

omit [DecidableEq Player] in
@[simp] theorem fromModeCompletion_toModeCompletion
    (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (completion : graph.Completion) :
    graph.fromModeCompletion mode (graph.toModeCompletion mode completion) =
      completion := by
  cases completion
  rfl

omit [DecidableEq Player] in
@[simp] theorem toModeCompletion_fromModeCompletion
    (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (completion : (graph.withMode mode).Completion) :
    graph.toModeCompletion mode (graph.fromModeCompletion mode completion) =
      completion := by
  cases completion
  rfl

omit [DecidableEq Player] in
@[simp] theorem fromModeObservation_toModeObservation
    (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (who : Player) (observation : graph.PlayerObservation who) :
    graph.fromModeObservation mode who
      (graph.toModeObservation mode who observation) = observation := by
  cases observation
  simp [toModeObservation, fromModeObservation, Function.comp_def]

omit [DecidableEq Player] in
@[simp] theorem toModeObservation_fromModeObservation
    (graph : Vegas.EventGraph Player L) (mode : ExecutionMode)
    (who : Player) (observation : (graph.withMode mode).PlayerObservation who) :
    graph.toModeObservation mode who
      (graph.fromModeObservation mode who observation) = observation := by
  cases observation
  simp [toModeObservation, fromModeObservation, Function.comp_def]

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
theorem toModeObservation_sequential
    (graph : Vegas.EventGraph Player L) (who : Player)
    (observation : graph.PlayerObservation who) :
    graph.toModeObservation .sequential who observation =
      graph.toSequentialObservation who observation := by
  apply PlayerObservation.ext graph.sequentialize
  · rfl
  · rfl
  · simp only [toModeObservation, toSequentialObservation]
    apply List.map_congr_left
    intro completion _
    cases completion
    rfl

omit [DecidableEq Player] in
@[simp] theorem fromModeProfile_concurrent
    (graph : Vegas.EventGraph Player L)
    (profile : (graph.withMode .concurrent).BehavioralProfile) :
    graph.fromModeProfile .concurrent profile = profile := by
  funext who event actor observation
  simp [fromModeProfile, fromModePolicy]

omit [DecidableEq Player] in
theorem fromModeProfile_sequential
    (graph : Vegas.EventGraph Player L)
    (profile : (graph.withMode .sequential).BehavioralProfile) :
    graph.fromModeProfile .sequential profile =
      graph.fromSequentialProfile profile := by
  funext who event actor observation
  simp only [fromModeProfile, fromModePolicy, fromSequentialProfile,
    fromSequentialPolicy]
  rw [graph.toModeObservation_sequential who observation]

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
      rw [graph.fromModeProfile_sequential profile]
      simpa using
          graph.canonical_fromSequential_store_law profile inputs

end Vegas.EventGraph
