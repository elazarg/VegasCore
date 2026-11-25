module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ExclusionCompletion

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

end Vegas.EventGraphRuntime.State
