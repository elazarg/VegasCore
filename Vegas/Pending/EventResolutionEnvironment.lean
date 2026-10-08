/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication

/-! # Environment commands cannot create a successful revelation

A resolve node succeeds only through an accepted opening. Sampling other
nodes, clock advancement, and expiry preserve absence of a successful result;
expiry at this node can only publish failure. The property is independent of
scheduling, pending-message visibility, source utilities, and equilibrium.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every primitive application environment command preserves a resolve
node's absence of success. No inclusion or player response is an environment
command in this application interface. -/
theorem environmentStep_resolution_no_success
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (command : EnvironmentCommand graph)
    (before : ∀ value : L.Val payload,
      cast (congrArg Option (congrArg EventField.Value outputEq))
        (state.config.outputs event) ≠ some (.success value))
    (reached : next ∈ (environmentStep runtime state command).support) :
    ∀ value : L.Val payload,
      cast (congrArg Option (congrArg EventField.Value outputEq))
        (next.config.outputs event) ≠ some (.success value) := by
  classical
  have other {config : graph.Config} {completed : graph.EventId}
      {ready : state.config.cut.Ready completed} {action : graph.Action completed}
      (different : event ≠ completed)
      (moved : config ∈ (state.config.step completed ready action).support) :
      config.outputs event = state.config.outputs event := by
    rw [Config.step, PMF.support_map] at moved
    obtain ⟨value, _supported, rfl⟩ := moved
    exact state.config.complete_output_of_ne completed event ready action value different
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact before
  | executeSample selected =>
      by_cases same : selected = event
      · subst selected
        by_cases ready : state.config.cut.Ready event
        · rw [environmentStep_executeSample_of_nonsample runtime state event ready
            (by intro _ _ _ _ sample; rw [node] at sample; cases sample),
            PMF.mem_support_pure_iff _ _] at reached
          subst next
          exact before
        · rw [environmentStep_executeSample_of_not_ready runtime state event ready,
            PMF.mem_support_pure_iff _ _] at reached
          subst next
          exact before
      · obtain ⟨_clock, unchanged | ⟨_ready, _action, stepped, _activated⟩⟩ :=
          environmentStep_executeSample_config_activated runtime state next selected reached
        · simpa only [unchanged.1] using before
        · simpa only [other (Ne.symm same) stepped] using before
  | expire selected =>
      by_cases same : selected = event
      · subst selected
        by_cases ready : state.config.cut.Ready event
        · cases activated : state.activatedAt event with
          | none =>
              rw [environmentStep_expire_of_not_activated runtime state event ready activated,
                PMF.mem_support_pure_iff _ _] at reached
              subst next
              exact before
          | some entered =>
              by_cases due : runtime.deadline event ≤ state.clock - entered
              · rw [environmentStep_expire_resolve_eq runtime state event ready entered
                  activated due owner payload binding checks outputEq codeEq node,
                  PMF.mem_support_pure_iff _ _] at reached
                subst next
                intro value
                rw [State.complete, Config.complete_output_same]
                have transported {first second : EventField Player L} (same : first = second)
                    (result : second.Value) :
                    cast (congrArg Option (congrArg EventField.Value same))
                      (some (cast (congrArg EventField.Value same.symm) result)) =
                        some result := by
                  cases same
                  rfl
                rw [transported outputEq]
                intro impossible
                cases (Option.some.inj impossible)
              · rw [environmentStep_expire_of_not_due runtime state event ready entered
                  activated due, PMF.mem_support_pure_iff _ _] at reached
                subst next
                exact before
        · rw [environmentStep_expire_of_not_ready runtime state event ready,
            PMF.mem_support_pure_iff _ _] at reached
          subst next
          exact before
      · obtain ⟨_clock, unchanged | ⟨_ready, _action, stepped, _activated⟩⟩ :=
          environmentStep_expire_config_activated runtime state next selected reached
        · simpa only [unchanged.1] using before
        · simpa only [other (Ne.symm same) stepped] using before

end Vegas.EventGraphRuntime
