/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Sequential
import Vegas.EventGraph.CanonicalNormalization
import Vegas.EventGraph.StateCongruence

/-! # Canonical semantics of sequential dependency specialization -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Transport one completion record without changing its event or action. -/
private def toSequentialCompletion (graph : Vegas.EventGraph Player L)
    (completion : graph.Completion) : graph.sequentialize.Completion :=
  ⟨completion.event, completion.action⟩

/-- Transport one sequential completion record back to the original graph. -/
private def fromSequentialCompletion (graph : Vegas.EventGraph Player L)
    (completion : graph.sequentialize.Completion) : graph.Completion :=
  ⟨completion.event, completion.action⟩

/-- Transport an original player observation to the sequential graph. -/
def toSequentialObservation (graph : Vegas.EventGraph Player L) (who : Player)
    (observation : graph.PlayerObservation who) :
    graph.sequentialize.PlayerObservation who where
  completionOrder := observation.completionOrder
  store := observation.store
  ownActions := observation.ownActions.map graph.toSequentialCompletion

/-- Transport a sequential player observation back to the original graph. -/
private def fromSequentialObservation (graph : Vegas.EventGraph Player L) (who : Player)
    (observation : graph.sequentialize.PlayerObservation who) :
    graph.PlayerObservation who where
  completionOrder := observation.completionOrder
  store := observation.store
  ownActions := observation.ownActions.map graph.fromSequentialCompletion

omit [DecidableEq Player] in
@[simp] private theorem fromSequentialCompletion_toSequentialCompletion
    (graph : Vegas.EventGraph Player L) (completion : graph.Completion) :
    graph.fromSequentialCompletion (graph.toSequentialCompletion completion) = completion := by
  cases completion
  rfl

omit [DecidableEq Player] in
@[simp] private theorem toSequentialCompletion_fromSequentialCompletion
    (graph : Vegas.EventGraph Player L)
    (completion : graph.sequentialize.Completion) :
    graph.toSequentialCompletion (graph.fromSequentialCompletion completion) = completion := by
  cases completion
  rfl

omit [DecidableEq Player] in
@[simp] private theorem fromSequentialObservation_toSequentialObservation
    (graph : Vegas.EventGraph Player L) (who : Player)
    (observation : graph.PlayerObservation who) :
    graph.fromSequentialObservation who
      (graph.toSequentialObservation who observation) = observation := by
  apply PlayerObservation.ext graph
  · rfl
  · rfl
  · simp only [fromSequentialObservation, toSequentialObservation, List.map_map]
    rw [show graph.fromSequentialCompletion ∘ graph.toSequentialCompletion = id by
      funext completion
      simp]
    exact List.map_id observation.ownActions

omit [DecidableEq Player] in
@[simp] private theorem toSequentialObservation_fromSequentialObservation
    (graph : Vegas.EventGraph Player L) (who : Player)
    (observation : graph.sequentialize.PlayerObservation who) :
    graph.toSequentialObservation who
      (graph.fromSequentialObservation who observation) = observation := by
  apply PlayerObservation.ext graph.sequentialize
  · rfl
  · rfl
  · simp only [fromSequentialObservation, toSequentialObservation, List.map_map]
    rw [show graph.toSequentialCompletion ∘ graph.fromSequentialCompletion = id by
      funext completion
      simp]
    exact List.map_id observation.ownActions

/-- Reuse a policy on the sequential dependency specialization after
transporting its observation. -/
def toSequentialPolicy (graph : Vegas.EventGraph Player L) (who : Player)
    (policy : graph.BehavioralPolicy who) :
  graph.sequentialize.BehavioralPolicy who :=
  fun event actor observation =>
    policy event (by exact actor)
      (graph.fromSequentialObservation who observation)

/-- Reuse a sequential-specialization policy on the original graph. -/
def fromSequentialPolicy (graph : Vegas.EventGraph Player L) (who : Player)
    (policy : graph.sequentialize.BehavioralPolicy who) :
  graph.BehavioralPolicy who :=
  fun event actor observation =>
    policy event (by exact actor)
      (graph.toSequentialObservation who observation)

/-- Transport a complete profile to the sequential dependency specialization. -/
def toSequentialProfile (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) :
    graph.sequentialize.BehavioralProfile :=
  fun who => graph.toSequentialPolicy who (profile who)

/-- Transport a complete profile back to the original graph. -/
def fromSequentialProfile (graph : Vegas.EventGraph Player L)
    (profile : graph.sequentialize.BehavioralProfile) :
    graph.BehavioralProfile :=
  fun who => graph.fromSequentialPolicy who (profile who)

/-- Forget the additional sequential dependencies in a coherent configuration.
Every dependency of the original graph is an earlier event, hence is already
closed in the sequential cut. -/
private def fromSequentialConfig (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) : graph.Config where
  inputs := config.inputs
  cut :=
    { completed := config.cut.completed
      predecessor_closed := by
        intro event completed predecessor predecessorMem
        apply config.cut.predecessor_closed completed
        exact (EventOrder.sequential.mem_predecessors predecessor event).2
          (graph.order.predecessor_lt predecessorMem) }
  outputs := config.outputs
  output_available := config.output_available
  history := config.history.map graph.fromSequentialCompletion
  history_nodup := by
    have events :
        (config.history.map graph.fromSequentialCompletion).map Completion.event =
          config.history.map Completion.event := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro completion _
      rfl
    rw [events]
    exact config.history_nodup
  history_exact := by
    intro event
    have events :
        (config.history.map graph.fromSequentialCompletion).map Completion.event =
          config.history.map Completion.event := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro completion _
      rfl
    rw [events]
    exact config.history_exact event

omit [DecidableEq Player] in
@[simp] private theorem fromSequentialConfig_inputs (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) :
    (graph.fromSequentialConfig config).inputs = config.inputs := rfl

omit [DecidableEq Player] in
@[simp] private theorem fromSequentialConfig_outputs (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) :
    (graph.fromSequentialConfig config).outputs = config.outputs := rfl

omit [DecidableEq Player] in
@[simp] private theorem fromSequentialConfig_completed (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) :
    (graph.fromSequentialConfig config).cut.completed = config.cut.completed := rfl

omit [DecidableEq Player] in
@[simp] private theorem fromSequentialConfig_store (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) :
    (graph.fromSequentialConfig config).store = config.store := by
  funext field
  cases field <;> rfl

omit [DecidableEq Player] in
@[simp] private theorem fromSequentialConfig_initial (graph : Vegas.EventGraph Player L)
    (inputs : graph.Inputs) :
    graph.fromSequentialConfig (Config.initial (graph := graph.sequentialize) inputs) =
      Config.initial (graph := graph) inputs := rfl

omit [DecidableEq Player] in
private theorem Config.eq_of_data_eq {graph : Vegas.EventGraph Player L}
    {left right : graph.Config} (inputs : left.inputs = right.inputs)
    (cut : left.cut = right.cut) (outputs : left.outputs = right.outputs)
    (history : left.history = right.history) : left = right := by
  cases left
  cases right
  simp_all

omit [DecidableEq Player] in
private theorem fromSequentialReady (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) :
    (graph.fromSequentialConfig config).cut.Ready event := by
  constructor
  · exact ready.1
  · intro predecessor member
    exact ready.2 ((EventOrder.sequential.mem_predecessors predecessor event).2
      (graph.order.predecessor_lt member))

omit [DecidableEq Player] in
@[simp] private theorem fromSequentialConfig_terminal (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) :
    (graph.fromSequentialConfig config).cut.Terminal ↔ config.cut.Terminal := by
  rfl

private theorem fromSequential_playerObserve (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) (who : Player) :
    graph.fromSequentialObservation who
        (graph.sequentialize.playerObserve who config) =
      graph.playerObserve who (graph.fromSequentialConfig config) := by
  apply PlayerObservation.ext graph
  · change config.history.map Completion.event =
      (config.history.map graph.fromSequentialCompletion).map Completion.event
    rw [List.map_map]
    symm
    apply List.map_congr_left
    intro completion _
    rfl
  · change graph.playerStore who config.store =
      graph.playerStore who (graph.fromSequentialConfig config).store
    rw [fromSequentialConfig_store]
  · simp only [fromSequentialObservation, playerObserve, ownCompletions,
      fromSequentialConfig]
    induction config.history with
    | nil => rfl
    | cons completion history ih =>
        simp only [List.filter_cons, List.map_cons]
        have actorEq : graph.sequentialize.actor? completion.event =
            graph.actor? completion.event := rfl
        rw [actorEq]
        split <;> simp_all [fromSequentialCompletion]

omit [DecidableEq Player] in
private theorem toSequentialObservation_normalizeObservation
    (graph : Vegas.EventGraph Player L) (event : graph.EventId) (who : Player)
    (observation : graph.PlayerObservation who) :
    graph.toSequentialObservation who (graph.normalizeObservation event who observation) =
      graph.sequentialize.normalizeObservation event who
        (graph.toSequentialObservation who observation) := by
  apply PlayerObservation.ext graph.sequentialize
  · rfl
  · rfl
  · rfl

private theorem normalizedObservation_fromSequentialConfig
    (graph : Vegas.EventGraph Player L) (config : graph.sequentialize.Config)
    (event : graph.EventId) (who : Player) :
    graph.toSequentialObservation who
        (graph.normalizeObservation event who
          (graph.playerObserve who (graph.fromSequentialConfig config))) =
      graph.sequentialize.normalizeObservation event who
        (graph.sequentialize.playerObserve who config) := by
  rw [← graph.fromSequential_playerObserve config who]
  rw [graph.toSequentialObservation_normalizeObservation]
  rw [toSequentialObservation_fromSequentialObservation]

omit [DecidableEq Player] in
private theorem fromSequentialConfig_complete (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    graph.fromSequentialConfig (config.complete event ready action value) =
      (graph.fromSequentialConfig config).complete event
        (graph.fromSequentialReady config event ready) action value := by
  apply Config.eq_of_data_eq
  · rfl
  · apply EventOrder.Cut.ext
    rfl
  · rfl
  · simp [fromSequentialConfig, Config.complete, fromSequentialCompletion]

omit [DecidableEq Player] in
private theorem fromSequentialConfig_step (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    (config.step event ready action).map graph.fromSequentialConfig =
      (graph.fromSequentialConfig config).step event
        (graph.fromSequentialReady config event ready) action := by
  let law := ((graph.sequentialize.nodes event).eval? action config.store).get
    (EventCode.eval?_isSome_of_reads (graph.sequentialize.nodes event) action config.store
      (fun _ read => config.read_available ready read))
  have sequentialEvaluates :
      (graph.sequentialize.nodes event).eval? action config.store = some law := by
    exact Option.eq_some_of_isSome
      (EventCode.eval?_isSome_of_reads (graph.sequentialize.nodes event) action config.store
        (fun _ read => config.read_available ready read))
  have originalEvaluates :
      (graph.nodes event).eval? action (graph.fromSequentialConfig config).store = some law := by
    rw [fromSequentialConfig_store]
    exact sequentialEvaluates
  rw [config.step_eq_map_of_eval event ready action law sequentialEvaluates]
  rw [(graph.fromSequentialConfig config).step_eq_map_of_eval event
    (graph.fromSequentialReady config event ready) action law originalEvaluates]
  rw [FinDist.map_comp]
  apply congrArg (fun function => law.map function)
  funext value
  exact graph.fromSequentialConfig_complete config event ready action value

private theorem normalizedPolicyStep_fromSequential (graph : Vegas.EventGraph Player L)
    (profile : graph.sequentialize.BehavioralProfile)
    (config : graph.sequentialize.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) :
    (graph.sequentialize.normalizedPolicyStep profile config event ready).map
        graph.fromSequentialConfig =
      graph.normalizedPolicyStep (graph.fromSequentialProfile profile)
        (graph.fromSequentialConfig config) event
        (graph.fromSequentialReady config event ready) := by
  unfold normalizedPolicyStep
  simp only [actor?, sequentialize_nodes]
  split
  · rename_i who actor
    split
    · rename_i originalWho originalActor
      have same : originalWho = who := Option.some.inj (originalActor.symm.trans actor)
      subst originalWho
      simp only [FinDist.map_bind]
      unfold normalizePolicy fromSequentialProfile fromSequentialPolicy
      rw [graph.normalizedObservation_fromSequentialConfig config event who]
      apply FinDist.bind_congr
      intro action _
      exact graph.fromSequentialConfig_step config event ready action
    · rename_i ownerless
      have impossible : (some who : Option Player) = none := actor.symm.trans ownerless
      cases impossible
  · rename_i ownerless
    split
    · rename_i who actor
      have impossible : (none : Option Player) = some who := ownerless.symm.trans actor
      cases impossible
    · exact graph.fromSequentialConfig_step config event ready
        (EventCode.actionOfActorNone (graph.sequentialize.nodes event) ownerless)

private theorem runPlan_canonical_fromSequential
    (graph : Vegas.EventGraph Player L)
    (profile : graph.sequentialize.BehavioralProfile) :
    ∀ fuel (config : graph.sequentialize.Config),
      (graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan
          (graph.sequentialize.normalizeProfile profile)
          graph.sequentialize.canonicalScheduler)
        fuel config).map graph.fromSequentialConfig =
      graph.runPlan
        (graph.policyPlan
          (graph.normalizeProfile (graph.fromSequentialProfile profile))
          graph.canonicalScheduler)
        fuel (graph.fromSequentialConfig config) := by
  intro fuel
  induction fuel with
  | zero =>
      intro config
      simp [runPlan]
  | succ fuel ih =>
      intro config
      by_cases terminal : config.cut.Terminal
      · have originalTerminal :
          (graph.fromSequentialConfig config).cut.Terminal := by
          simpa using terminal
        simp [runPlan, terminal, originalTerminal]
      · let event := config.cut.enabled.min'
          (enabled_nonempty_of_not_terminal config terminal)
        have ready : config.cut.Ready event :=
          (EventOrder.Cut.mem_enabled _ _).mp (Finset.min'_mem _ _)
        have least : ∀ other, other ∉ config.cut.completed →
            event.val ≤ other.val :=
          (canonical_min_ready_is_least_unfinished config.cut terminal).2
        have originalNotTerminal :
            ¬ (graph.fromSequentialConfig config).cut.Terminal := by
          simpa using terminal
        have originalReady := graph.fromSequentialReady config event ready
        have originalLeast : ∀ other,
            other ∉ (graph.fromSequentialConfig config).cut.completed →
              event.val ≤ other.val := by
          intro other unfinished
          exact least other unfinished
        rw [graph.sequentialize.runPlan_canonical_normalized_step
          profile fuel config event ready least]
        rw [graph.runPlan_canonical_normalized_step
          (graph.fromSequentialProfile profile) fuel
          (graph.fromSequentialConfig config) event originalReady originalLeast]
        rw [FinDist.map_bind]
        calc
          _ = (graph.sequentialize.normalizedPolicyStep profile config event ready).bind
                (fun next => graph.runPlan
                  (graph.policyPlan
                    (graph.normalizeProfile (graph.fromSequentialProfile profile))
                    graph.canonicalScheduler)
                  fuel (graph.fromSequentialConfig next)) := by
              apply FinDist.bind_congr
              intro next _
              exact ih next
          _ = ((graph.sequentialize.normalizedPolicyStep profile config event ready).map
                graph.fromSequentialConfig).bind
                (graph.runPlan
                  (graph.policyPlan
                  (graph.normalizeProfile (graph.fromSequentialProfile profile))
                    graph.canonicalScheduler)
                  fuel) := by
              rw [FinDist.bind_map]
          _ = _ := by
              rw [graph.normalizedPolicyStep_fromSequential profile config event ready]

/-- Canonical execution of the sequential dependency specialization has the
same terminal store law as canonical execution of the original graph after
forgetting the dependency mode from the profile. -/
theorem canonical_fromSequential_store_law
    (graph : Vegas.EventGraph Player L)
    (profile : graph.sequentialize.BehavioralProfile)
    (inputs : graph.Inputs) :
    (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
      profile inputs).map Config.store =
    (graph.runPolicies graph.canonicalScheduler
      (graph.fromSequentialProfile profile) inputs).map Config.store := by
  rw [graph.sequentialize.runPolicies_canonical_normalize_eq profile inputs]
  rw [graph.runPolicies_canonical_normalize_eq
    (graph.fromSequentialProfile profile) inputs]
  let law := graph.sequentialize.runPlan
      (graph.sequentialize.policyPlan
        (graph.sequentialize.normalizeProfile profile)
        graph.sequentialize.canonicalScheduler)
      graph.order.eventCount (Config.initial inputs)
  have transported : law.map graph.fromSequentialConfig =
      graph.runPlan
        (graph.policyPlan
          (graph.normalizeProfile (graph.fromSequentialProfile profile))
          graph.canonicalScheduler)
        graph.order.eventCount
          (graph.fromSequentialConfig (Config.initial inputs)) :=
    graph.runPlan_canonical_fromSequential profile graph.order.eventCount
      (Config.initial inputs)
  change law.map Config.store =
    (graph.runPlan
      (graph.policyPlan
        (graph.normalizeProfile (graph.fromSequentialProfile profile))
        graph.canonicalScheduler)
      graph.order.eventCount (Config.initial inputs)).map Config.store
  calc
    law.map Config.store =
        (law.map graph.fromSequentialConfig).map Config.store := by
        rw [FinDist.map_comp]
        apply congrArg (fun function => law.map function)
        funext config
        exact (graph.fromSequentialConfig_store config).symm
    _ = _ := by
        rw [transported, graph.fromSequentialConfig_initial]

end Vegas.EventGraph
