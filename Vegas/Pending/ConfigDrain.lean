module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ExclusionCompletion
public import Vegas.EventGraph.OwnedStep

@[expose] public section

/-! # Automatic completion as a deterministic function of a graph configuration -/

noncomputable section

namespace Vegas.EventGraphRuntime.State

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L}

/-- The runtime state of a configuration with the initial runtime tables. -/
def ofConfig (config : graph.Config) : State graph :=
  { State.initial config.inputs with config := config }

/-- The configuration reached by draining a configuration. -/
def drainConfig (config : graph.Config) : graph.Config := (ofConfig config).drain.config

private theorem drainFuel_config_congr (fuel : Nat) (left right : State graph)
    (same : left.config = right.config) :
    (drainFuel fuel left).config = (drainFuel fuel right).config := by
  induction fuel generalizing left right with
  | zero => exact same
  | succ fuel ih =>
    obtain ⟨config, accepted, candidates, clock, activated⟩ := left
    obtain ⟨_, _, _, _, _⟩ := right
    cases same
    simp only [drainFuel, AutomaticReady]
    split <;> rename_i pending
    · apply ih
      unfold completeAutomatic completeFailure
      cases nodeView graph (Classical.choose pending) <;> rfl
    · rfl

/-- The exact automatic-completion configuration is independent of all runtime tables. -/
theorem drain_config_eq (state : State graph) :
    state.drain.config = drainConfig state.config :=
  drainFuel_config_congr _ state (ofConfig state.config) rfl

/-- Automatic completion fixes the configuration at a quiescent state. -/
theorem drainConfig_of_quiescent (state : State graph)
    (quiet : ∀ event, ¬ state.AutomaticReady event) :
    drainConfig state.config = state.config := by
  rw [← drain_config_eq state, drain_eq_of_clear state quiet]

/-- Completing an already drained configuration is idempotent. -/
theorem drainConfig_drain_eq (state : State graph) :
    drainConfig state.drain.config = drainConfig state.config := by
  rw [drainConfig_of_quiescent state.drain state.drain_quiescent, state.drain_config_eq]

/-- When an automatic event is the sole ready event, draining it and then
continuing automatic service recovers the original drain. -/
theorem drain_eq_completeAutomatic_of_unique (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event)
    (unique : ∀ other, state.config.cut.Ready other → other = event) :
    state.drain = (state.completeAutomatic event eligible).drain := by
  classical
  have progress := state.completeAutomatic_progress event eligible
  unfold drain
  rw [← progress, drainFuel]
  split
  · rename_i pending
    have chosen := Classical.choose_spec pending
    have same := unique _ chosen.1
    generalize_proofs _ at *
    cases same
    rfl
  · exact False.elim (‹¬ ∃ other, state.AutomaticReady other› ⟨event, eligible⟩)

/-- A ready defaulted event with no competing ready event is complete after
the automatic drain. -/
theorem drainConfig_completed_of_defaulted (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (unique : ∀ other, config.cut.Ready other → other = event)
    (owner : Player) (owned : graph.actor? event = some owner)
    (inactive : owner ∈ config.defaulted) :
    event ∈ (drainConfig config).cut.completed := by
  let state := ofConfig config
  have eligible : state.AutomaticReady event := by
    refine ⟨ready, ?_⟩
    rw [owned]
    exact inactive
  change event ∈ state.drain.config.cut.completed
  rw [state.drain_eq_completeAutomatic_of_unique event eligible unique]
  apply EventGraph.Config.Step.path_completed_mono
    (state.completeAutomatic event eligible).drain_graph_steps
  obtain ⟨action, taken⟩ := state.completeAutomatic_step event eligible
  rw [state.config.step_cut event eligible.1 action _ taken, EventOrder.Cut.mem_complete]
  exact Or.inl rfl

/-- A defaulted solitary head can be advanced in the graph after the ledger has
already drained it. The graph step followed by another drain recovers the
same exact native configuration, for every requested action. -/
theorem step_drainConfig_of_defaulted (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (unique : ∀ other, config.cut.Ready other → other = event)
    (owner : Player) (owned : graph.actor? event = some owner)
    (inactive : owner ∈ config.defaulted) (action : graph.Action event) :
    (config.step event ready action).map drainConfig = PMF.pure (drainConfig config) := by
  let state := ofConfig config
  have eligible : state.AutomaticReady event := by
    refine ⟨ready, ?_⟩
    rw [owned]
    exact inactive
  obtain ⟨forced, supported⟩ := state.completeAutomatic_step event eligible
  obtain ⟨next, step⟩ := config.step_eq_pure_of_actor event ready forced owner owned
  have realized : (state.completeAutomatic event eligible).config = next := by
    change (state.completeAutomatic event eligible).config ∈
      (config.step event ready forced).support at supported
    rwa [step, PMF.mem_support_pure_iff] at supported
  have drained := state.drain_eq_completeAutomatic_of_unique event eligible unique
  rw [config.step_eq_of_defaulted event ready owner owned inactive action forced, step,
    PMF.pure_map, ← realized, ← drain_config_eq, ← drained, drain_config_eq]
  rfl

end Vegas.EventGraphRuntime.State
