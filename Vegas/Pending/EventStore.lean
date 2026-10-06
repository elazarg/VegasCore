/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventProgress

/-! # Immutable event-store prefixes

Once a typed field is available, no native action changes its value. This
includes arbitrary player commands, malformed traffic, and expiry.
Endpoint-conditioned replay may therefore read an earlier public result from
a later observation without adding that observation to a runtime policy.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

namespace EventGraphRuntime

/-- Any accepted packet retains every already stored typed value. -/
theorem handle_store_of_some (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : state.config.store field = some value) :
    next.config.store field = some value := by
  obtain ⟨event, _, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  exact state.config.step_store_of_some next.config event ready action member field value stored

omit [DecidableEq Player] in
/-- Chance, clocks, and expiry preserve every field already present. -/
theorem environmentStep_store_of_some (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : state.config.store field = some value) :
    next.config.store field = some value := by
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff _ _] at member
      subst next
      exact stored
  | executeSample event =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_executeSample_config_activated runtime state next event member
      · rw [stutter.1]
        exact stored
      · obtain ⟨ready, action, member, _⟩ := step
        exact state.config.step_store_of_some next.config event ready action member
          field value stored
  | expire event =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_expire_config_activated runtime state next event member
      · rw [stutter.1]
        exact stored
      · obtain ⟨ready, action, member, _⟩ := step
        exact state.config.step_store_of_some next.config event ready action member
          field value stored

omit [DecidableEq Player] in
/-- An environment operation only appends semantic completions; it cannot
remove or replace an action already recorded in the graph history. -/
theorem environmentStep_history_prefix (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support) :
    state.config.history.IsPrefix next.config.history := by
  have fromStep (event : graph.EventId) (ready : state.config.cut.Ready event)
      (action : graph.Action event)
      (supported : next.config ∈ (state.config.step event ready action).support) :
      state.config.history.IsPrefix next.config.history := by
    rw [state.config.step_history event ready action next.config supported]
    exact ⟨_, rfl⟩
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff _ _] at member
      subst next
      exact ⟨[], by simp⟩
  | executeSample event =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_executeSample_config_activated runtime state next event member
      · rw [stutter.1]
      · obtain ⟨ready, action, supported, _⟩ := step
        exact fromStep event ready action supported
  | expire event =>
      obtain ⟨_, stutter | step⟩ :=
        environmentStep_expire_config_activated runtime state next event member
      · rw [stutter.1]
      · obtain ⟨ready, action, supported, _⟩ := step
        exact fromStep event ready action supported

end EventGraphRuntime
end Vegas
