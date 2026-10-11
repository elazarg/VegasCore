/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRetainedFrontier
import Vegas.Pending.ReactiveDeviationRecall
import Vegas.Pending.ReactiveDeviationObservation
import Vegas.Pending.ReactiveDeviationCompletion

/-! # Retained frontiers for one arbitrary raw player -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Foreign players retain genuine sampled intentions. The arbitrary focal
player instead retains its actual physical completions and has no fictitious
prescribed memory. Both configurations use the unchanged graph semantics. -/
structure ReactiveUnilateralFrontier (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (focal : Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config) : Prop
    extends runtime.ReactiveRetainedFrontier leaks execution memories frontier where
  empty : memories focal = []
  intentions : ∀ owner, graph.ownCompletions owner frontier.history =
    if owner = focal then graph.ownCompletions owner execution.application.config.history
    else (memories owner).filterMap id

/-- A genuinely retained intention belongs to a foreign player because the
arbitrary focal player has no prescribed memory. -/
theorem ReactiveUnilateralFrontier.retained_foreign (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (owner : Player) (retained : ∃ saved, some saved ∈ memories owner) : owner ≠ focal := by
  intro same
  subst owner
  obtain ⟨saved, member⟩ := retained
  simp [related.empty] at member

/-- The mixed relation begins at the actual initialized execution, without
any policy restriction on the focal player. -/
theorem reactiveUnilateralFrontier_initial (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (inputs : graph.Inputs) :
    runtime.ReactiveUnilateralFrontier leaks focal
      (ReactiveApplication.Execution.initial
        (runtime.reactiveApplication leaks) (State.initial inputs))
      (fun _ => []) (Config.initial inputs) := by
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · exact .initial
    · rfl
    · intro event
      simp [ReactiveApplication.Execution.initial, State.initial, Config.initial,
        EventOrder.Cut.empty]
    · exact Config.CompletedOutputAgreement.refl _
    · intro owner
      exact ⟨[], rfl⟩
  · intro owner
    simp [Config.initial, ReactiveApplication.Execution.initial, State.initial, ownCompletions]

/-- Every arbitrary raw focal callback preserves the retained frontier. Its
physical graph state stutters and every foreign intention is retained. -/
theorem ReactiveUnilateralFrontier.respond_focal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (action : (runtime.reactiveApplication leaks).Action) :
    runtime.ReactiveUnilateralFrontier leaks focal
      (execution.respond (runtime.reactiveApplication leaks) focal action) memories frontier := by
  have configEq := (runtime.reactive_respond_application leaks execution focal action).1
  have originalEq := runtime.originalConfig_respond_of_empty_memory leaks execution memories
    focal related.empty action
  refine ⟨?_, related.empty, ?_⟩
  · constructor
    · rw [configEq]
      exact related.reachable
    · rw [configEq]
      exact related.inputs
    · intro event
      rw [configEq]
      exact related.domain event
    · rw [configEq]
      exact related.settled
    · intro owner
      rw [originalEq]
      exact related.recalled owner
  · intro owner
    rw [configEq]
    exact related.intentions owner

/-- A common actual focal graph draw advances both existing configurations and
retains the mixed source recall relation. No focal prescribed policy is used. -/
theorem ReactiveUnilateralFrontier.complete_focal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (physicalReady : execution.application.config.cut.Ready event)
    (frontierReady : frontier.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    (physicalSupported : execution.application.config.complete event physicalReady action value ∈
      (execution.application.config.step event physicalReady action).support)
    (frontierSupported : frontier.complete event frontierReady action value ∈
      (frontier.step event frontierReady action).support)
    (entries : List (runtime.reactiveApplication leaks).EnvironmentEntry) :
    runtime.ReactiveUnilateralFrontier leaks focal
      { execution with
        application := execution.application.complete event physicalReady action value
        environmentRecall := entries }
      memories (frontier.complete event frontierReady action value) := by
  let next : (runtime.reactiveApplication leaks).Execution :=
    { execution with
      application := execution.application.complete event physicalReady action value
      environmentRecall := entries }
  have originalEq := runtime.originalConfig_complete_focal leaks execution memories focal
    related.empty event physicalReady actor action value entries
  have ownAppend (owner : Player) (config : graph.Config) (ready : config.cut.Ready event) :
      graph.ownCompletions owner (config.complete event ready action value).history =
        graph.ownCompletions owner config.history ++
          (if owner = focal then [(⟨event, action⟩ : graph.Completion)] else []) := by
    simp only [Config.complete, ownCompletions, List.filter_append]
    apply congrArg (List.append _)
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
    simp [actor, eq_comm]
  refine ⟨?_, related.empty, ?_⟩
  · constructor
    · exact related.reachable.step event frontierReady action _ frontierSupported
    · exact related.inputs
    · intro query
      change query ∈ insert event frontier.cut.completed ↔
        query ∈ insert event execution.application.config.cut.completed ∨ _
      simp only [Finset.mem_insert, related.domain query]
      tauto
    · apply Config.CompletedOutputAgreement.physical_step _ _ _
        (related.settled.frontier_step _ _ _ event frontierReady action frontierSupported)
        event physicalReady action physicalSupported
      simp
    · intro owner
      change graph.ownCompletions owner (runtime.originalConfig leaks next memories).history <+: _
      rw [originalEq, ownAppend, ownAppend]
      by_cases same : owner = focal
      · subst owner
        have actualRecall := congrArg PlayerObservation.ownActions
          (runtime.originalConfig_playerObserve_of_empty_memory leaks execution memories focal
            related.empty)
        change graph.ownCompletions focal
          (runtime.originalConfig leaks execution memories).history =
          graph.ownCompletions focal execution.application.config.history at actualRecall
        rw [actualRecall, related.intentions focal]
        simp
      · simpa only [same, ↓reduceIte, List.append_nil] using related.recalled owner
  · intro owner
    change graph.ownCompletions owner (frontier.complete event frontierReady action value).history =
      if owner = focal then
        graph.ownCompletions owner
          (execution.application.config.complete event physicalReady action value).history
      else (memories owner).filterMap id
    rw [ownAppend, related.intentions owner]
    by_cases same : owner = focal
    · simp only [same, ↓reduceIte, ownAppend]
    · simp only [same, ↓reduceIte, List.append_nil]

/-- Genuine focal graph transitions preserve the mixed relation whenever their
actual reconstructed recall appends the identified native action. This premise
is supplied by native accepted-envelope and expiry identification. -/
theorem ReactiveUnilateralFrontier.step_focal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution next : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier final : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (physicalReady : execution.application.config.cut.Ready event)
    (frontierReady : frontier.cut.Ready event) (action : graph.Action event)
    (physicalSupported : next.application.config ∈
      (execution.application.config.step event physicalReady action).support)
    (frontierSupported : final ∈ (frontier.step event frontierReady action).support)
    (settled : next.application.config.CompletedOutputAgreement final)
    (sameInputs : next.application.config.inputs = final.inputs)
    (sourceHistory : (runtime.originalConfig leaks next memories).history =
      (runtime.originalConfig leaks execution memories).history ++ [⟨event, action⟩]) :
    runtime.ReactiveUnilateralFrontier leaks focal next memories final := by
  have physicalInputs : next.application.config.inputs = execution.application.config.inputs := by
    rw [Config.step, PMF.support_map] at physicalSupported
    obtain ⟨value, _, produced⟩ := physicalSupported
    rw [← produced]
    rfl
  have appendOwn (owner : Player) (history : List graph.Completion) :
      graph.ownCompletions owner (history ++ [⟨event, action⟩]) =
        graph.ownCompletions owner history ++
          (if owner = focal then [(⟨event, action⟩ : graph.Completion)] else []) := by
    simp only [ownCompletions, List.filter_append]
    apply congrArg (List.append _)
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
    simp [actor, eq_comm]
  have physicalHistory := execution.application.config.step_history event physicalReady action
    next.application.config physicalSupported
  have frontierHistory := frontier.step_history event frontierReady action final frontierSupported
  refine ⟨?_, related.empty, ?_⟩
  · constructor
    · rw [physicalInputs]
      exact related.reachable.step event frontierReady action final frontierSupported
    · exact sameInputs.symm
    · intro query
      rw [frontier.step_cut event frontierReady action final frontierSupported,
        execution.application.config.step_cut event physicalReady action next.application.config
          physicalSupported]
      simp only [EventOrder.Cut.mem_complete, related.domain query]
      tauto
    · exact settled
    · intro owner
      rw [sourceHistory, frontierHistory, appendOwn, appendOwn]
      by_cases same : owner = focal
      · subst owner
        have actualRecall := congrArg PlayerObservation.ownActions
          (runtime.originalConfig_playerObserve_of_empty_memory leaks execution memories focal
            related.empty)
        change graph.ownCompletions focal
          (runtime.originalConfig leaks execution memories).history =
            graph.ownCompletions focal execution.application.config.history at actualRecall
        rw [actualRecall, related.intentions focal]
        simp
      · simpa only [same, ↓reduceIte, List.append_nil] using related.recalled owner
  · intro owner
    rw [frontierHistory, appendOwn, related.intentions owner]
    by_cases same : owner = focal
    · simp only [same, ↓reduceIte, physicalHistory, appendOwn]
    · simp only [same, ↓reduceIte, List.append_nil]

end Vegas.EventGraphRuntime
