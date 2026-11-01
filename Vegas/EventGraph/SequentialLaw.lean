/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Sequential
import Vegas.EventGraph.CanonicalStep

/-! # Canonical semantics of sequential dependency specialization -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Forget the additional sequential dependencies in a coherent configuration.
Every dependency of the original graph is an earlier event, hence is already
closed in the sequential cut. -/
def fromSequentialConfig (graph : Vegas.EventGraph Player L)
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
  history := config.history
  history_nodup := config.history_nodup
  history_exact := config.history_exact

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

omit [DecidableEq Player] in
/-- Forgetting sequential prerequisites preserves the entire public default history. -/
@[simp] theorem fromSequentialConfig_defaults (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) :
    (graph.fromSequentialConfig config).defaults = config.defaults := rfl

/-- Forgetting sequential prerequisites preserves the derived default set. -/
@[simp] theorem fromSequentialConfig_defaulted (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) :
    (graph.fromSequentialConfig config).defaulted = config.defaulted := by
  change (graph.fromSequentialConfig config).defaults.defaulted = config.defaults.defaulted
  rw [fromSequentialConfig_defaults]

private theorem fromSequential_playerObserve (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) (who : Player) :
    graph.sequentialize.playerObserve who config =
      graph.playerObserve who (graph.fromSequentialConfig config) := by
  apply EventPlayerObservation.ext
  · rfl
  · change graph.playerStore who config.store =
      graph.playerStore who (graph.fromSequentialConfig config).store
    rw [fromSequentialConfig_store]
  · rfl
  · rfl

private theorem fromSequentialConfig_complete (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    graph.fromSequentialConfig (config.complete event ready action value) =
      (graph.fromSequentialConfig config).complete event
        (graph.fromSequentialReady config event ready) action value := by
  have actual : (graph.fromSequentialConfig config).actualDecision event action =
      config.actualDecision event action := by
    unfold Config.actualDecision
    rw [fromSequentialConfig_defaulted]
    rfl
  apply Config.eq_of_data_eq
  · rfl
  · apply EventOrder.Cut.ext
    rfl
  · rfl
  · change List.append (config.history : List graph.Completion)
        [graph.sequentialize.completion event (config.actualDecision event action) value] =
      List.append (config.history : List graph.Completion) [graph.completion event
        ((graph.fromSequentialConfig config).actualDecision event action) value]
    rw [actual]
    rfl

private theorem fromSequentialConfig_step (graph : Vegas.EventGraph Player L)
    (config : graph.sequentialize.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    (config.step event ready action).map graph.fromSequentialConfig =
      (graph.fromSequentialConfig config).step event
        (graph.fromSequentialReady config event ready) action := by
  let effective := config.effectiveAction event action
  let law := ((graph.sequentialize.nodes event).eval? effective config.store).get
    (EventCode.eval?_isSome_of_reads (graph.sequentialize.nodes event) effective config.store
      (fun _ read => config.read_available ready read))
  have sequentialEvaluates :
      (graph.sequentialize.nodes event).eval? effective config.store = some law := by
    exact Option.eq_some_of_isSome
      (EventCode.eval?_isSome_of_reads (graph.sequentialize.nodes event) effective config.store
        (fun _ read => config.read_available ready read))
  have originalEffective : (graph.fromSequentialConfig config).effectiveAction event action =
      effective := by
    unfold Config.effectiveAction
    rw [fromSequentialConfig_defaulted]
    rfl
  have originalEvaluates :
      (graph.nodes event).eval?
        ((graph.fromSequentialConfig config).effectiveAction event action)
        (graph.fromSequentialConfig config).store = some law := by
    rw [fromSequentialConfig_store, originalEffective]
    exact sequentialEvaluates
  rw [config.step_eq_map_of_eval event ready action law sequentialEvaluates]
  rw [(graph.fromSequentialConfig config).step_eq_map_of_eval event
    (graph.fromSequentialReady config event ready) action law originalEvaluates]
  rw [PMF.map_comp]
  apply congrArg (fun function => law.map function)
  funext value
  exact graph.fromSequentialConfig_complete config event ready action value

/-- Canonical execution transports the full configuration when sequential
prerequisites are forgotten; both sides use their ordinary graph executor. -/
theorem runPlan_canonical_fromSequential
    (graph : Vegas.EventGraph Player L) (profile : graph.sequentialize.BehavioralProfile) :
    ∀ fuel (config : graph.sequentialize.Config),
      (graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        fuel config).map graph.fromSequentialConfig =
      graph.runPlan
        (graph.policyPlan profile graph.canonicalScheduler)
        fuel (graph.fromSequentialConfig config) := by
  intro fuel
  induction fuel with
  | zero =>
      intro config
      simp [runPlan, PMF.pure_map]
  | succ fuel ih =>
      intro config
      by_cases terminal : config.cut.Terminal
      · have originalTerminal : (graph.fromSequentialConfig config).cut.Terminal := terminal
        simp [runPlan, terminal, originalTerminal, PMF.pure_map]
      · let event := config.cut.enabled.min'
          (enabled_nonempty_of_not_terminal config terminal)
        have ready : config.cut.Ready event :=
          (EventOrder.Cut.mem_enabled _ _).mp (Finset.min'_mem _ _)
        have least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val :=
          (canonical_min_ready_is_least_unfinished config.cut terminal).2
        have originalReady := graph.fromSequentialReady config event ready
        have originalLeast : ∀ other,
            other ∉ (graph.fromSequentialConfig config).cut.completed →
              event.val ≤ other.val := fun other unfinished => least other unfinished
        have continuation (action : graph.Action event) :
            ((config.step event ready action).bind
              (graph.sequentialize.runPlan
                (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
                fuel)).map graph.fromSequentialConfig =
            ((graph.fromSequentialConfig config).step event originalReady action).bind
              (graph.runPlan
                (graph.policyPlan profile
                  graph.canonicalScheduler) fuel) := by
          rw [PMF.map_bind]
          calc
            _ = (config.step event ready action).bind fun next =>
                  graph.runPlan
                    (graph.policyPlan profile
                      graph.canonicalScheduler) fuel (graph.fromSequentialConfig next) := by
                apply bind_congr_on_support _
                intro next _
                exact ih next
            _ = ((config.step event ready action).map graph.fromSequentialConfig).bind
                  (graph.runPlan
                    (graph.policyPlan profile
                      graph.canonicalScheduler) fuel) := by
                rw [PMF.bind_map, Function.comp_def]
            _ = _ := by rw [graph.fromSequentialConfig_step config event ready action]
        cases actor : graph.actor? event with
        | none =>
            have sequentialActor : graph.sequentialize.actor? event = none := actor
            rw [graph.sequentialize.runPlan_canonical_ownerless profile fuel config event ready
              least sequentialActor, graph.runPlan_canonical_ownerless
                profile fuel (graph.fromSequentialConfig config)
                event originalReady originalLeast actor]
            exact continuation _
        | some who =>
            have sequentialActor : graph.sequentialize.actor? event = some who := actor
            by_cases inactive : who ∈ config.defaulted
            · have originalInactive : who ∈ (graph.fromSequentialConfig config).defaulted := by
                rwa [fromSequentialConfig_defaulted]
              let action := (graph.nodes event).failureAction who actor
              rw [graph.sequentialize.runPlan_canonical_defaulted profile fuel config event ready
                least who sequentialActor inactive action, graph.runPlan_canonical_defaulted
                  profile fuel
                  (graph.fromSequentialConfig config)
                  event originalReady originalLeast who actor originalInactive action]
              exact continuation action
            · have originalActive : who ∉ (graph.fromSequentialConfig config).defaulted := by
                rwa [fromSequentialConfig_defaulted]
              rw [graph.sequentialize.runPlan_canonical_actor profile fuel config event ready least
                who sequentialActor inactive, graph.runPlan_canonical_actor
                  profile fuel
                  (graph.fromSequentialConfig config)
                  event originalReady originalLeast who actor originalActive, PMF.map_bind]
              have kernel :
                  profile who event actor
                      (graph.playerObserve who (graph.fromSequentialConfig config))
                      originalActive =
                    profile who event sequentialActor
                      (graph.sequentialize.playerObserve who config) inactive := by
                congr 1
                exact (graph.fromSequential_playerObserve config who).symm
              rw [kernel]
              apply bind_congr_on_support _
              intro action _
              exact continuation action

/-- Sequential specialization and the original graph have the same complete
canonical execution law after forgetting only the added dependencies. -/
theorem canonical_fromSequential_config_law
    (graph : Vegas.EventGraph Player L) (profile : graph.sequentialize.BehavioralProfile)
    (inputs : graph.Inputs) :
    (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler profile inputs).map
        graph.fromSequentialConfig =
      graph.runPolicies graph.canonicalScheduler
        profile inputs := by
  exact graph.runPlan_canonical_fromSequential profile graph.order.eventCount
    (Config.initial inputs)

/-- Canonical sequential specialization retains the exact typed terminal-store law. -/
theorem canonical_fromSequential_store_law
    (graph : Vegas.EventGraph Player L) (profile : graph.sequentialize.BehavioralProfile)
    (inputs : graph.Inputs) :
    (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler profile inputs).map
        Config.store =
      (graph.runPolicies graph.canonicalScheduler
        profile inputs).map Config.store := by
  have full := congrArg (PMF.map Config.store)
    (graph.canonical_fromSequential_config_law profile inputs)
  simpa only [PMF.map_comp, Function.comp_def, fromSequentialConfig_store] using full

end Vegas.EventGraph
