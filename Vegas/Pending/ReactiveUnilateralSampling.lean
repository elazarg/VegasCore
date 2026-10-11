/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnilateralFrontier
import Vegas.Pending.ReactiveFrontier

/-! # Genuine foreign sampling with an arbitrary raw focal player -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Supported foreign memories cannot contain a fresh event under another
actor, even when the focal player has no prescribed memory or policy. -/
theorem ReactiveUnilateralFrontier.ready_foreign (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile) (execution : (runtime.reactiveApplication leaks).Execution)
    (focal : Player) (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (who : Player) (event : graph.EventId)
    (actor : graph.actor? event = some who)
    (ready : execution.application.config.cut.Ready event)
    (fresh : event ∉ (memories who).filterMap (fun saved => saved.map Completion.event)) :
    frontier.cut.Ready event := by
  constructor
  · intro completed
    rcases (related.domain event).mp completed with physical | ⟨owner, remembered, member, named⟩
    · exact ready.1 physical
    · by_cases same : owner = focal
      · subst owner
        simp [related.empty] at member
      · have owned := runtime.prescribedReactivePosterior_owned leaks owner (profile owner)
          (consistent owner same) (memories owner) (supported owner same) remembered member
        rw [named, actor, Option.some.injEq] at owned
        subst owner
        exact fresh (List.mem_filterMap.mpr ⟨some remembered, member, by simp [named]⟩)
  · intro predecessor dependency
    exact (related.domain predecessor).mpr (Or.inl (ready.2 dependency))

/-- A genuine foreign prescribed response samples its own action into the
reachable frontier while retaining the arbitrary focal player's actual recall. -/
theorem ReactiveUnilateralFrontier.respond_foreign_some (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner))
    (supportedMemory : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (who : Player) (different : who ≠ focal)
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
      runtime.ReactiveUnilateralFrontier leaks focal
        (execution.respond (runtime.reactiveApplication leaks) who action)
        (Function.update memories who (memories who ++ [some remembered])) next := by
  obtain ⟨physicalReady, actor⟩ := runtime.prescribedReactiveResponse_some_ready leaks who
    (profile who) (execution.recall who) (memories who)
    (execution.observe (runtime.reactiveApplication leaks) who) action remembered supported
  have fresh := runtime.prescribedReactiveResponse_event_not_saved leaks who (profile who)
    (consistent who different) quiet sent (memories who) (supportedMemory who different)
    (execution.observe (runtime.reactiveApplication leaks) who) action remembered supported
  have ready := related.ready_foreign runtime leaks profile execution focal memories frontier
    consistent supportedMemory who remembered.event actor
    ((execution.application.publicView_eventReady remembered.event).mp physicalReady) fresh
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
  refine ⟨?_, ?_, ?_⟩
  · constructor
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
      rw [semanticKey_ownCompletions_eq originalSame owner, ownEq]
      exact (related.recalled owner).trans (List.prefix_append _ _)
  · rw [Function.update_of_ne different.symm]
    exact related.empty
  · intro owner
    rw [ownEq, related.intentions owner, configEq]
    by_cases equal : owner = who
    · subst owner
      simp [different, List.filterMap_append]
    · simp only [equal, ↓reduceIte, List.append_nil, Function.update_of_ne equal]

theorem ReactiveUnilateralFrontier.respond_foreign_none (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (who : Player) (different : who ≠ focal) (policy : graph.BehavioralPolicy who)
    (aligned : (execution.recall who).length = (memories who).length)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : (action, none) ∈
      (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) (memories who)
        (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    runtime.ReactiveUnilateralFrontier leaks focal
      (execution.respond (runtime.reactiveApplication leaks) who action)
      (Function.update memories who (memories who ++ [none])) frontier := by
  have configEq := (runtime.reactive_respond_application leaks execution who action).1
  have originalSame := runtime.originalConfig_respond_semanticKey leaks execution memories who
    policy aligned action none supported
  refine ⟨?_, ?_, ?_⟩
  · constructor
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
      rw [semanticKey_ownCompletions_eq originalSame owner]
      exact related.recalled owner
  · rw [Function.update_of_ne different.symm]
    exact related.empty
  · intro owner
    rw [related.intentions owner, configEq]
    by_cases equal : owner = who
    · subst owner
      simp [different, List.filterMap_append]
    · simp only [Function.update_of_ne equal]

end Vegas.EventGraphRuntime
