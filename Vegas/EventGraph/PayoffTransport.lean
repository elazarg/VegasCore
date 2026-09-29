/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Information

/-! # Changing declared payoffs preserves event execution

Payoff expressions are terminal readouts. Replacing them changes neither a
ready event's actions nor its transition law. The explicit configuration
transport below preserves inputs, outputs, cuts and complete action histories;
it therefore applies to adaptive plans and every possible deviation, not only
to prescribed runs.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

def withPayoffs (graph : Vegas.EventGraph Player L)
    (payoffs : List (Player × PublicExpr graph.layout L.int)) :
    Vegas.EventGraph Player L :=
  { graph with payoffs := payoffs }

variable (graph : Vegas.EventGraph Player L)
    (payoffs : List (Player × PublicExpr graph.layout L.int))

def completionWithPayoffs (completion : graph.Completion) :
    (graph.withPayoffs payoffs).Completion :=
  ⟨completion.event, completion.action⟩

def completionWithoutPayoffs (completion : (graph.withPayoffs payoffs).Completion) :
    graph.Completion :=
  ⟨completion.event, completion.action⟩

@[simp] theorem completionWithoutPayoffs_withPayoffs (completion : graph.Completion) :
    graph.completionWithoutPayoffs payoffs (graph.completionWithPayoffs payoffs completion) =
      completion := by cases completion; rfl

@[simp] theorem completionWithPayoffs_withoutPayoffs
    (completion : (graph.withPayoffs payoffs).Completion) :
    graph.completionWithPayoffs payoffs (graph.completionWithoutPayoffs payoffs completion) =
      completion := by cases completion; rfl

def configWithPayoffs (config : graph.Config) : (graph.withPayoffs payoffs).Config where
  inputs := config.inputs
  cut := config.cut
  outputs := config.outputs
  output_available := config.output_available
  history := config.history.map (graph.completionWithPayoffs payoffs)
  history_nodup := by
    simpa only [List.map_map, Function.comp_def, completionWithPayoffs]
      using config.history_nodup
  history_exact := by
    intro event
    simpa only [List.map_map, Function.comp_def, completionWithPayoffs]
      using config.history_exact event

def configWithoutPayoffs (config : (graph.withPayoffs payoffs).Config) : graph.Config where
  inputs := config.inputs
  cut := config.cut
  outputs := config.outputs
  output_available := config.output_available
  history := config.history.map (graph.completionWithoutPayoffs payoffs)
  history_nodup := by
    simpa only [List.map_map, Function.comp_def, completionWithoutPayoffs]
      using config.history_nodup
  history_exact := by
    intro event
    simpa only [List.map_map, Function.comp_def, completionWithoutPayoffs]
      using config.history_exact event

@[simp] theorem configWithoutPayoffs_withPayoffs (config : graph.Config) :
    graph.configWithoutPayoffs payoffs (graph.configWithPayoffs payoffs config) = config := by
  cases config
  simp [configWithoutPayoffs, configWithPayoffs, List.map_map, Function.comp_def]

@[simp] theorem configWithPayoffs_withoutPayoffs
    (config : (graph.withPayoffs payoffs).Config) :
    graph.configWithPayoffs payoffs (graph.configWithoutPayoffs payoffs config) = config := by
  cases config
  simp [configWithoutPayoffs, configWithPayoffs, List.map_map, Function.comp_def]

def configPayoffEquiv : graph.Config ≃ (graph.withPayoffs payoffs).Config where
  toFun := graph.configWithPayoffs payoffs
  invFun := graph.configWithoutPayoffs payoffs
  left_inv := graph.configWithoutPayoffs_withPayoffs payoffs
  right_inv := graph.configWithPayoffs_withoutPayoffs payoffs

@[simp] theorem configWithPayoffs_store (config : graph.Config) :
    (graph.configWithPayoffs payoffs config).store = config.store := by
  funext field
  cases field <;> rfl

@[simp] theorem configWithPayoffs_initial (inputs : graph.Inputs) :
    graph.configWithPayoffs payoffs (Config.initial inputs) =
      Config.initial (graph := graph.withPayoffs payoffs) inputs := rfl

@[simp] theorem configWithPayoffs_complete (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    graph.configWithPayoffs payoffs (config.complete event ready action value) =
      (graph.configWithPayoffs payoffs config).complete event ready action value := by
  simp only [configWithPayoffs, Config.complete, List.map_append, List.map_cons, List.map_nil]
  rfl

/-- Payoff replacement commutes with every legal action, including chance. -/
theorem configWithPayoffs_step (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    (config.step event ready action).map (graph.configWithPayoffs payoffs) =
      (graph.configWithPayoffs payoffs config).step event ready action := by
  simp only [Config.step, PMF.map_comp, Function.comp_def, configWithPayoffs_complete,
    configWithPayoffs_store]
  rfl

/-- The transported plan can inspect exactly the same full configuration. -/
def planWithPayoffs (plan : graph.EventPlan) : (graph.withPayoffs payoffs).EventPlan :=
  fun config unfinished => plan (graph.configWithoutPayoffs payoffs config) unfinished

theorem planWithPayoffs_config (plan : graph.EventPlan) (config : graph.Config)
    (unfinished : ¬ config.cut.Terminal) :
    graph.planWithPayoffs payoffs plan (graph.configWithPayoffs payoffs config) unfinished =
      plan config unfinished := by
  unfold planWithPayoffs
  congr 1
  exact graph.configWithoutPayoffs_withPayoffs payoffs config

theorem runPlan_withPayoffs (plan : graph.EventPlan) (fuel : Nat) (config : graph.Config) :
    ((graph.withPayoffs payoffs).runPlan (graph.planWithPayoffs payoffs plan) fuel
      (graph.configWithPayoffs payoffs config)) =
      (graph.runPlan plan fuel config).map (graph.configWithPayoffs payoffs) := by
  induction fuel generalizing config with
  | zero => simp only [runPlan, PMF.pure_map]
  | succ fuel ih =>
      simp only [runPlan]
      by_cases terminal : config.cut.Terminal
      · simp only [show (graph.configWithPayoffs payoffs config).cut = config.cut from rfl,
          terminal, dite_true, PMF.pure_map]
      · simp only [show (graph.configWithPayoffs payoffs config).cut = config.cut from rfl,
          terminal, dite_false, planWithPayoffs_config, PMF.map_bind]
        apply congrArg (PMF.bind (plan config _))
        funext choice
        rw [← configWithPayoffs_step, PMF.bind_map]
        apply congrArg (PMF.bind (config.step choice.1.1 choice.1.2 choice.2))
        funext next
        exact ih next

/-- A declared payoff replacement preserves the entire operational run law. -/
theorem run_withPayoffs (plan : graph.EventPlan) (inputs : graph.Inputs) :
    (graph.withPayoffs payoffs).run inputs (graph.planWithPayoffs payoffs plan) =
      (graph.run inputs plan).map (graph.configWithPayoffs payoffs) := by
  exact graph.runPlan_withPayoffs payoffs plan graph.order.eventCount (Config.initial inputs)

variable [DecidableEq Player]

def publicObservationWithPayoffs (observation : graph.PublicObservation) :
    (graph.withPayoffs payoffs).PublicObservation :=
  ⟨observation.completionOrder, observation.store⟩

def playerObservationWithPayoffs (who : Player) (observation : graph.PlayerObservation who) :
    (graph.withPayoffs payoffs).PlayerObservation who :=
  ⟨observation.completionOrder, observation.store,
    observation.ownActions.map (graph.completionWithPayoffs payoffs)⟩

omit [DecidableEq Player] in
/-- The full public observation is retained, including completion order. -/
theorem publicObserve_withPayoffs (config : graph.Config) :
    (graph.withPayoffs payoffs).publicObserve (graph.configWithPayoffs payoffs config) =
      graph.publicObservationWithPayoffs payoffs (graph.publicObserve config) := by
  apply PublicObservation.ext
  · simp only [publicObserve, configWithPayoffs, publicObservationWithPayoffs,
      List.map_map, Function.comp_def, completionWithPayoffs]
  · simp only [publicObserve, publicObservationWithPayoffs, configWithPayoffs_store]
    rfl

/-- Each player retains the same visible store and complete own-action recall. -/
theorem playerObserve_withPayoffs (who : Player) (config : graph.Config) :
    (graph.withPayoffs payoffs).playerObserve who (graph.configWithPayoffs payoffs config) =
      graph.playerObservationWithPayoffs payoffs who (graph.playerObserve who config) := by
  apply PlayerObservation.ext
  · simp only [playerObserve, configWithPayoffs, playerObservationWithPayoffs,
      List.map_map, Function.comp_def, completionWithPayoffs]
  · simp only [playerObserve, playerObservationWithPayoffs, configWithPayoffs_store]
    rfl
  · simp only [playerObserve, playerObservationWithPayoffs, configWithPayoffs,
      ownCompletions, List.filter_map, Function.comp_def, completionWithPayoffs,
      actor?, withPayoffs]

end Vegas.EventGraph
