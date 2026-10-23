/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseRequestProgress
import Vegas.Pending.EventCommandFrame

/-! # A ready physical coordinate is insulated from other environment work -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Unrelated expiry, chance execution and clock advances preserve the selected
request. Automatic closure cannot retire a phase while this event remains ready. -/
theorem environment_other_request (runtime : EventGraphRuntime graph)
    (ordered : graph.RevealRelaxedOrdered)
    (state next : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph)
    (reached : next ∈ (state.environment runtime command).support)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : state.SeedRequest owner coordinate)
    (other : command ≠ .expire coordinate.event) :
    next.SeedRequest owner coordinate := by
  classical
  unfold PhaseRuntimeState.environment at reached
  split at reached
  · obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    have completed := environmentStep_owned_completed_iff runtime state.current.native native
      command coordinate.event owner requested.2.2.2.1 other moved
    have unfinished : coordinate.event ∉ native.config.cut.completed :=
      fun member => requested.2.2.1.1 (completed.mp member)
    have ready : native.config.cut.Ready coordinate.event := by
      refine ⟨unfinished, ?_⟩
      exact requested.2.2.1.2.trans
        (environmentStep_completed_subset runtime state.current.native native command moved)
    have active : owner ∉ (state.current.environmentResult command native).excluded := by
      cases command with
      | advanceClock => exact requested.2.2.2.2
      | executeSample event => exact requested.2.2.2.2
      | expire event =>
          change owner ∉ (if event ∉ state.current.native.config.cut.completed ∧
              event ∈ native.config.cut.completed then
            RecoveryState.excludeEvent state.current.excluded event else state.current.excluded)
          split_ifs with changed
          · obtain ⟨_, effect⟩ := environmentStep_expire_config_activated runtime
              state.current.native native event moved
            rcases effect with ⟨config, _⟩ | ⟨eventReady, _action, _supported, _⟩
            · exact (changed.1 (config ▸ changed.2)).elim
            · have different : graph.actor? event ≠ some owner := by
                intro owned
                have same := ordered.ready_actor_unique state.current.native.config.cut
                  requested.2.2.1 eventReady requested.2.2.2.1 owned
                exact other (by cases same; rfl)
              unfold RecoveryState.excludeEvent
              cases acting : graph.actor? event with
              | none => exact requested.2.2.2.2
              | some actor =>
                  intro member
                  rcases Finset.mem_insert.mp member with same | already
                  · exact different (acting.trans (congrArg some same.symm))
                  · exact requested.2.2.2.2 already
          · exact requested.2.2.2.2
    let raw : PhaseRuntimeState graph :=
      { state with current := state.current.environmentResult command native }
    have retained : raw.SeedRequest owner coordinate :=
      ⟨requested.1, requested.2.1, ready, requested.2.2.2.1, active⟩
    exact retained.normalize.2
  · cases (PMF.mem_support_pure_iff _ _).mp reached
    exact requested

/-- At the application boundary every command either preserves the selected
request or is expiry of that exact selected event. In particular an unrelated
phase failure cannot retire a still-ready owner's physical address. -/
theorem environment_request_or_expiry (runtime : EventGraphRuntime graph)
    (ordered : graph.RevealRelaxedOrdered)
    (state next : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph)
    (reached : next ∈ (state.environment runtime command).support)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (requested : state.SeedRequest owner coordinate) :
    next.SeedRequest owner coordinate ∨ command = .expire coordinate.event := by
  by_cases same : command = .expire coordinate.event
  · exact Or.inr same
  · exact Or.inl (environment_other_request runtime ordered state next command reached
      owner coordinate requested same)

end PhaseRuntimeState
end Vegas.EventGraphRuntime
