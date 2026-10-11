/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDeviationRecall

/-! # Actual focal graph completions in retained configurations -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Completing the arbitrary focal player's event restores its actual action
in the source configuration. Foreign private memories remain unchanged. -/
theorem originalConfig_complete_focal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (focal : Player)
    (empty : memories focal = []) (event : graph.EventId)
    (ready : execution.application.config.cut.Ready event)
    (actor : graph.actor? event = some focal) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    (entries : List (runtime.reactiveApplication leaks).EnvironmentEntry) :
    runtime.originalConfig leaks
      { execution with
        application := execution.application.complete event ready action value
        environmentRecall := entries } memories =
      (runtime.originalConfig leaks execution memories).complete event ready action value := by
  let next : (runtime.reactiveApplication leaks).Execution :=
    { execution with
      application := execution.application.complete event ready action value
      environmentRecall := entries }
  apply Config.eq_of_fields
  · rfl
  · rfl
  · rfl
  · change (execution.application.config.history ++ [(⟨event, action⟩ : graph.Completion)]).map
      (runtime.originalCompletion leaks next memories) =
        (execution.application.config.history.map
          (runtime.originalCompletion leaks execution memories)) ++
            [(⟨event, action⟩ : graph.Completion)]
    rw [List.map_append, List.map_singleton]
    have previous : execution.application.config.history.map
        (runtime.originalCompletion leaks next memories) =
          execution.application.config.history.map
            (runtime.originalCompletion leaks execution memories) := rfl
    rw [previous]
    have current : runtime.originalCompletion leaks next memories ⟨event, action⟩ =
        ⟨event, action⟩ := by
      simp only [originalCompletion, actor, empty]
      cases node : nodeView graph event <;> simp [reactiveOriginal, node]
    rw [current]

/-- Every supported native expiry at the arbitrary focal player's event either
stutters the reconstructed configuration or performs its actual failure step.
Private foreign intention memories are retained without prescribed focal support. -/
theorem originalConfig_expire_focal_eq_or_mem_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution after : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (focal : Player)
    (empty : memories focal = []) (event : graph.EventId)
    (actor : graph.actor? event = some focal)
    (supported : after ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support) :
    runtime.originalConfig leaks after memories = runtime.originalConfig leaks execution memories ∨
      ∃ (ready : execution.application.config.cut.Ready event) (action : graph.Action event),
        runtime.originalConfig leaks after memories ∈
          ((runtime.originalConfig leaks execution memories).step event ready action).support := by
  unfold ReactiveApplication.Execution.environmentStep at supported
  obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ moved
  change state ∈ (runtime.environmentStep execution.application (.expire event)).support at changed
  rcases environmentStep_expire_config_eq_or_mem_step runtime execution.application state event
      changed with unchanged | ⟨ready, action, physical⟩
  · left
    apply Config.eq_of_fields
    · change state.config.inputs = execution.application.config.inputs
      exact congrArg Config.inputs unchanged
    · change state.config.cut = execution.application.config.cut
      exact congrArg Config.cut unchanged
    · change state.config.outputs = execution.application.config.outputs
      exact congrArg Config.outputs unchanged
    · change state.config.history.map (runtime.originalCompletion leaks _ memories) = _
      rw [unchanged]
      rfl
  · right
    rw [Config.step, PMF.support_map] at physical
    obtain ⟨value, valueSupported, produced⟩ := physical
    refine ⟨ready, action, ?_⟩
    have originalEq : runtime.originalConfig leaks
        { execution with application := state } memories =
        (runtime.originalConfig leaks execution memories).complete event ready action value := by
      apply Config.eq_of_fields
      · change state.config.inputs = execution.application.config.inputs
        rw [← produced]
        rfl
      · change state.config.cut = execution.application.config.cut.complete event ready
        rw [← produced]
        rfl
      · change state.config.outputs =
          (execution.application.config.complete event ready action value).outputs
        exact congrArg Config.outputs produced.symm
      · change state.config.history.map (runtime.originalCompletion leaks _ memories) =
          (runtime.originalConfig leaks execution memories).history ++ [⟨event, action⟩]
        rw [← produced]
        simp only [Config.complete, List.map_append, List.map_singleton]
        have originals : runtime.originalCompletion leaks
            { execution with application := state } memories =
              runtime.originalCompletion leaks execution memories := rfl
        rw [originals]
        have current : runtime.originalCompletion leaks execution memories ⟨event, action⟩ =
            ⟨event, action⟩ := by
          simp only [originalCompletion, actor, empty]
          cases node : nodeView graph event <;> simp [reactiveOriginal, node]
        rw [current]
        rfl
    change runtime.originalConfig leaks { execution with application := state } memories ∈
      ((runtime.originalConfig leaks execution memories).step event ready action).support
    rw [originalEq, Config.step, PMF.support_map]
    exact ⟨value, valueSupported, rfl⟩

end Vegas.EventGraphRuntime
