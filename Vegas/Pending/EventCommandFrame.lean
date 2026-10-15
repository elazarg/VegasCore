/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant

/-! # Environment commands preserve unrelated strategic events -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A chance command addressed to a strategic event stutters. -/
theorem environmentStep_executeSample_of_owned (runtime : EventGraphRuntime graph)
    (state : State graph) (event : graph.EventId) (owner : Player)
    (acting : graph.actor? event = some owner) :
    environmentStep runtime state (.executeSample event) = PMF.pure state := by
  by_cases ready : state.config.cut.Ready event
  · apply environmentStep_executeSample_of_nonsample runtime state event ready
    intro payload law outputEq codeEq _view
    have codeActor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq (graph.nodes event)] at codeActor
    have impossible : graph.actor? event = none := by
      simpa only [EventGraph.actor?, EventCode.actor] using codeActor
    rw [acting] at impossible
    cases impossible
  · exact environmentStep_executeSample_of_not_ready runtime state event ready

/-- Only expiry of this exact event can complete an owned event through an
application environment command. No assumption on other ready actors is needed. -/
theorem environmentStep_owned_completed_iff (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (event : graph.EventId) (owner : Player) (acting : graph.actor? event = some owner)
    (other : command ≠ .expire event)
    (reached : next ∈ (environmentStep runtime state command).support) :
    event ∈ next.config.cut.completed ↔ event ∈ state.config.cut.completed := by
  classical
  have stepOther (address : graph.EventId) (different : event ≠ address)
      (ready : state.config.cut.Ready address) (action : graph.Action address)
      (member : next.config ∈ (state.config.step address ready action).support) :
      event ∈ next.config.cut.completed ↔ event ∈ state.config.cut.completed := by
    rw [EventGraph.Config.step_cut state.config address ready action next.config member,
      EventOrder.Cut.mem_complete]
    simp only [different, false_or]
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff _ _] at reached
      cases reached
      exact Iff.rfl
  | expire address =>
      have different : event ≠ address := fun same => other (by cases same; rfl)
      rcases environmentStep_expire_config_eq_or_mem_step runtime state next address reached with
        config | ⟨ready, action, member⟩
      · rw [config]
      · exact stepOther address different ready action member
  | executeSample address =>
      by_cases same : event = address
      · subst address
        rw [environmentStep_executeSample_of_owned runtime state event owner acting,
          PMF.mem_support_pure_iff _ _] at reached
        cases reached
        exact Iff.rfl
      · obtain ⟨_, effect⟩ := environmentStep_executeSample_config_activated runtime state next
          address reached
        rcases effect with ⟨config, _⟩ | ⟨ready, action, member, _⟩
        · rw [config]
        · exact stepOther address same ready action member

end Vegas.EventGraphRuntime
