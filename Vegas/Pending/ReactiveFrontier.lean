/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePendingFrontierReadiness
import Vegas.Pending.ReactiveOriginalConfig
import Vegas.Pending.ReactiveSampledFrontierOwnership
import Vegas.Pending.ReactiveSampledFrontierFreshness
import Vegas.EventGraph.CompletedOutputAgreement
import Interaction.ReactiveRecall
import Interaction.ReactiveReceipts
/-! # Reachable semantic frontiers for retained reactive intentions -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- An existing reachable semantic execution has sampled each retained original
intention, while the physical execution may still be awaiting its settlement.
The relation records full owner chronology and available typed outputs. -/
structure ReactiveFrontier (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config) : Prop where
  reachable : frontier.Reachable execution.application.config.inputs
  inputs : frontier.inputs = execution.application.config.inputs
  domain : ∀ event, event ∈ frontier.cut.completed ↔
    event ∈ execution.application.config.cut.completed ∨
      ∃ owner remembered, some remembered ∈ memories owner ∧ remembered.event = event
  settled : execution.application.config.CompletedOutputAgreement frontier
  intentions : ∀ owner, graph.ownCompletions owner frontier.history = (memories owner).filterMap id
  recalled : ∀ owner, graph.ownCompletions owner
    (runtime.originalConfig leaks execution memories).history <+:
      graph.ownCompletions owner frontier.history

/-- The sampled frontier starts at the genuine graph initial configuration. -/
theorem reactiveFrontier_initial (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) :
    runtime.ReactiveFrontier leaks
      (ReactiveApplication.Execution.initial
        (runtime.reactiveApplication leaks) (State.initial inputs))
      (fun _ => []) (Config.initial inputs) := by
  constructor
  · exact .initial
  · rfl
  · intro event
    simp [ReactiveApplication.Execution.initial, State.initial, Config.initial,
      EventOrder.Cut.empty]
  · exact Config.CompletedOutputAgreement.refl _
  · intro owner
    rfl
  · intro owner
    exact ⟨[], rfl⟩

/-- A real supported response and its memory append preserve every original
completion already physically recorded, for all owners simultaneously. -/
theorem originalCompletion_respond_completed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (aligned : (execution.recall who).length = (memories who).length)
    (action : (runtime.reactiveApplication leaks).Action) (saved : Option graph.Completion)
    (supported : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) (memories who)
        (execution.observe (runtime.reactiveApplication leaks) who)).support)
    (completion : graph.Completion)
    (completed : completion.event ∈ execution.application.config.cut.completed) :
    runtime.originalCompletion leaks
      (execution.respond (runtime.reactiveApplication leaks) who action)
      (Function.update memories who (memories who ++ [saved])) completion =
        runtime.originalCompletion leaks execution memories completion := by
  cases actor : graph.actor? completion.event with
  | none => simp only [originalCompletion, actor]
  | some owner =>
      simp only [originalCompletion, actor]
      by_cases equal : owner = who
      · subst owner
        simp only [Function.update_self]
        exact runtime.reactiveOriginal_respond_completed leaks who policy execution (memories who)
          aligned action saved supported completion completed
      · rw [(runtime.reactiveApplication leaks).respond_recall_other
          execution who owner equal action,
          (runtime.reactiveApplication leaks).respond_receipts execution who action,
          Function.update_of_ne equal]

/-- Updating the actual response and all-owner memory leaves the complete
original physical semantic state fixed. -/
theorem originalConfig_respond_semanticKey (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (aligned : (execution.recall who).length = (memories who).length)
    (action : (runtime.reactiveApplication leaks).Action) (saved : Option graph.Completion)
    (supported : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) (memories who)
        (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    graph.semanticKey (runtime.originalConfig leaks
      (execution.respond (runtime.reactiveApplication leaks) who action)
      (Function.update memories who (memories who ++ [saved]))) =
        graph.semanticKey (runtime.originalConfig leaks execution memories) := by
  have configEq := (runtime.reactive_respond_application leaks execution who action).1
  have historyEq : (runtime.originalConfig leaks
      (execution.respond (runtime.reactiveApplication leaks) who action)
      (Function.update memories who (memories who ++ [saved]))).history =
        (runtime.originalConfig leaks execution memories).history := by
    change ((execution.respond
      (runtime.reactiveApplication leaks) who action).application.config.history.map
      (runtime.originalCompletion leaks _ _)) = _
    rw [configEq]
    apply List.map_congr_left
    intro completion retained
    exact runtime.originalCompletion_respond_completed leaks execution memories who policy aligned
      action saved supported completion
      ((execution.application.config.history_exact completion.event).mp
        (List.mem_map.mpr ⟨completion, retained, rfl⟩))
  apply Prod.ext
  · change (execution.respond
      (runtime.reactiveApplication leaks) who action).application.config.cut =
      execution.application.config.cut
    exact congrArg Config.cut configEq
  · apply Prod.ext
    · change (execution.respond
        (runtime.reactiveApplication leaks) who action).application.config.store =
        execution.application.config.store
      exact congrArg Config.store configEq
    · exact congrArg (fun history => fun owner => graph.ownCompletions owner history) historyEq
private theorem updatedIntentionEvents
    (memories : Player → List (Option graph.Completion)) (who : Player)
    (saved : Option graph.Completion) (query : graph.EventId) :
    (∃ owner remembered, some remembered ∈
        Function.update memories who (memories who ++ [saved]) owner ∧ remembered.event = query) ↔
      (∃ owner remembered, some remembered ∈ memories owner ∧ remembered.event = query) ∨
        saved.map Completion.event = some query := by
  constructor
  · rintro ⟨owner, remembered, retained, named⟩
    by_cases equal : owner = who
    · subst owner
      rw [Function.update_self] at retained
      rcases List.mem_append.mp retained with earlier | current
      · exact Or.inl ⟨who, remembered, earlier, named⟩
      · right
        have selected : some remembered = saved := List.mem_singleton.mp current
        rw [← selected]
        exact congrArg some named
    · rw [Function.update_of_ne equal] at retained
      exact Or.inl ⟨owner, remembered, retained, named⟩
  · rintro (⟨owner, remembered, retained, named⟩ | selected)
    · refine ⟨owner, remembered, ?_, named⟩
      by_cases equal : owner = who
      · subst owner
        rw [Function.update_self]
        exact List.mem_append_left _ retained
      · rw [Function.update_of_ne equal]
        exact retained
    · cases saved with
      | none => cases selected
      | some remembered =>
          exact ⟨who, remembered, by simp, Option.some.inj selected⟩

/-- An actual compiler callback that retains no new decision stutters the
reachable sampled frontier and preserves full reconstructed own recall. -/
theorem ReactiveFrontier.respond_none (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (who : Player) (policy : graph.BehavioralPolicy who)
    (aligned : (execution.recall who).length = (memories who).length)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : (action, none) ∈
      (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) (memories who)
        (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    runtime.ReactiveFrontier leaks
      (execution.respond (runtime.reactiveApplication leaks) who action)
      (Function.update memories who (memories who ++ [none])) frontier := by
  have configEq := (runtime.reactive_respond_application leaks execution who action).1
  have originalSame := runtime.originalConfig_respond_semanticKey leaks execution memories who
    policy aligned action none supported
  constructor
  · rw [configEq]
    exact related.reachable
  · rw [configEq]
    exact related.inputs
  · intro event
    rw [configEq, updatedIntentionEvents]
    simpa only [Option.map_none, reduceCtorEq, or_false] using related.domain event
  · rw [configEq]
    exact related.settled
  · intro owner
    by_cases equal : owner = who
    · subst owner
      simpa only [Function.update_self, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, id_eq, List.append_nil] using related.intentions who
    · rw [Function.update_of_ne equal]
      exact related.intentions owner
  · intro owner
    rw [semanticKey_ownCompletions_eq originalSame owner]
    exact related.recalled owner

/-- Every genuine newly retained compiler decision advances the existing
reachable graph execution by that exact original action. -/
theorem ReactiveFrontier.respond_some (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (who : Player)
    (quiet : ∀ entry ∈ execution.recall who,
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (aligned : (execution.recall who).length = (memories who).length)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
        (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    ∃ ready : frontier.cut.Ready remembered.event, ∃ next,
      next ∈ (frontier.step remembered.event ready remembered.action).support ∧
      runtime.ReactiveFrontier leaks
        (execution.respond (runtime.reactiveApplication leaks) who action)
        (Function.update memories who (memories who ++ [some remembered])) next := by
  obtain ⟨physicalReady, actor⟩ := runtime.prescribedReactiveResponse_some_ready leaks who
    (profile who) (execution.recall who) (memories who)
    (execution.observe (runtime.reactiveApplication leaks) who) action remembered supported
  have fresh := runtime.prescribedReactiveResponse_event_not_saved leaks who (profile who)
    (consistent who) quiet sent (memories who) (supportedMemory who)
    (execution.observe (runtime.reactiveApplication leaks) who) action remembered supported
  have ready := runtime.sampledFrontier_ready leaks profile execution memories consistent
    supportedMemory frontier related.domain who remembered.event
    ((execution.application.publicView_eventReady remembered.event).mp physicalReady) actor fresh
  obtain ⟨next, member⟩ := (frontier.step remembered.event ready remembered.action).support_nonempty
  refine ⟨ready, next, member, ?_⟩
  have configEq := (runtime.reactive_respond_application leaks execution who action).1
  have originalSame := runtime.originalConfig_respond_semanticKey leaks execution memories who
    (profile who) aligned action (some remembered) supported
  have historyEq := frontier.step_history remembered.event ready remembered.action next member
  have ownEq : ∀ owner, graph.ownCompletions owner next.history =
      graph.ownCompletions owner frontier.history ++
        (if owner = who then [remembered] else []) := by
    intro owner
    rw [historyEq]
    cases remembered with
    | mk event decision =>
      simp only [ownCompletions, List.filter_append, List.filter_cons, List.filter_nil]
      simp [actor, eq_comm]
  constructor
  · rw [configEq]
    exact related.reachable.step remembered.event ready remembered.action next member
  · rw [configEq]
    rw [Config.step, PMF.support_map] at member
    obtain ⟨value, _, rfl⟩ := member
    exact related.inputs
  · intro event
    rw [frontier.step_cut remembered.event ready remembered.action next member,
      EventOrder.Cut.mem_complete, configEq, updatedIntentionEvents]
    simp only [Option.map_some, Option.some.injEq]
    rw [related.domain event]
    constructor
    · rintro (equal | completed | retained)
      · exact Or.inr (Or.inr equal.symm)
      · exact Or.inl completed
      · exact Or.inr (Or.inl retained)
    · rintro (completed | retained | equal)
      · exact Or.inr (Or.inl completed)
      · exact Or.inr (Or.inr retained)
      · exact Or.inl equal.symm
  · rw [configEq]
    exact related.settled.frontier_step _ _ _ remembered.event ready remembered.action member
  · intro owner
    rw [ownEq, related.intentions owner]
    by_cases equal : owner = who
    · subst owner
      simp [List.filterMap_append]
    · simp [equal]
  · intro owner
    rw [semanticKey_ownCompletions_eq originalSame owner, ownEq]
    exact (related.recalled owner).trans (List.prefix_append _ _)

end Vegas.EventGraphRuntime
