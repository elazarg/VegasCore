/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFrontier

/-! # The unique pending owner suffix in original recall -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability

private theorem prefix_append_unique_pending {α β : Type} (event : α → β)
    (past future : List α) (remembered : α)
    (ordered : past <+: future)
    (unique : (future.map event).Nodup)
    (present : remembered ∈ future)
    (unfinished : event remembered ∉ past.map event)
    (onlyPending : ∀ completion ∈ future,
      event completion ∉ past.map event → event completion = event remembered) :
    future = past ++ [remembered] := by
  obtain ⟨pending, rfl⟩ := ordered
  have pendingMember : remembered ∈ pending := by
    rcases List.mem_append.mp present with earlier | later
    · exact False.elim (unfinished (List.mem_map.mpr ⟨remembered, earlier, rfl⟩))
    · exact later
  have distinct := List.nodup_append.mp (by simpa only [List.map_append] using unique)
  have pendingEvent : ∀ completion ∈ pending, event completion = event remembered := by
    intro completion member
    apply onlyPending completion (List.mem_append_right _ member)
    intro earlier
    obtain ⟨old, oldMember, same⟩ := List.mem_map.mp earlier
    exact distinct.2.2 (event completion)
      (List.mem_map.mpr ⟨old, oldMember, same⟩)
      (event completion) (List.mem_map.mpr ⟨completion, member, rfl⟩) rfl
  cases pending with
  | nil => simp at pendingMember
  | cons first rest =>
    have empty : rest = [] := by
      by_contra nonempty
      obtain ⟨other, member⟩ := List.exists_mem_of_ne_nil rest nonempty
      have same := (pendingEvent first (by simp)).trans
        (pendingEvent other (List.mem_cons_of_mem _ member)).symm
      have forbidden := (List.nodup_cons.mp distinct.2.1).1
      exact forbidden (List.mem_map.mpr ⟨other, member, same.symm⟩)
    subst rest
    have same : remembered = first := List.mem_singleton.mp pendingMember
    subst first
    rfl

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Compilation barriers and actual posterior readiness force the next unsettled
owned intention to be the entire remaining own-recall suffix. -/
theorem ReactiveFrontier.pending_owner_suffix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (who : Player) (remembered : graph.Completion)
    (retained : some remembered ∈ memories who)
    (ready : execution.application.config.cut.Ready remembered.event) :
    graph.ownCompletions who frontier.history =
      graph.ownCompletions who (runtime.originalConfig leaks execution memories).history ++
        [remembered] := by
  let original := runtime.originalConfig leaks execution memories
  have actor := runtime.prescribedReactivePosterior_owned leaks who (profile who)
    (consistent who) (memories who) (supported who) remembered retained
  have eventDomain : ∀ event, graph.actor? event = some who →
      (event ∈ (graph.ownCompletions who original.history).map Completion.event ↔
        event ∈ execution.application.config.cut.completed) := by
    intro event owned
    constructor
    · rintro member
      obtain ⟨completion, member, named⟩ := List.mem_map.mp member
      exact (original.history_exact event).mp
        (List.mem_map.mpr ⟨completion, (List.mem_filter.mp member).1, named⟩)
    · intro completed
      obtain ⟨completion, member, named⟩ := List.mem_map.mp
        ((original.history_exact event).mpr completed)
      exact List.mem_map.mpr ⟨completion, List.mem_filter.mpr
        ⟨member, by simpa only [named, decide_eq_true_eq] using owned⟩, named⟩
  apply prefix_append_unique_pending Completion.event _ _ remembered (related.recalled who)
  · exact frontier.history_nodup.sublist (List.filter_sublist.map _)
  · rw [related.intentions who]
    exact List.mem_filterMap.mpr ⟨some remembered, retained, rfl⟩
  · exact fun member => ready.1 ((eventDomain remembered.event actor).mp member)
  · intro completion member unfinished
    have completionActor : graph.actor? completion.event = some who :=
      of_decide_eq_true (List.mem_filter.mp member).2
    have physicalUnfinished : completion.event ∉ execution.application.config.cut.completed :=
      fun completed => unfinished ((eventDomain completion.event completionActor).mpr completed)
    have ghostCompleted := (frontier.history_exact completion.event).mp
      (List.mem_map.mpr ⟨completion, (List.mem_filter.mp member).1, rfl⟩)
    obtain ⟨owner, saved, savedMember, sameEvent⟩ :=
      (related.domain completion.event).mp ghostCompleted |>.resolve_left physicalUnfinished
    have pendingReady := runtime.prescribedReactivePosterior_pending_ready leaks execution stable
      owner (profile owner) (consistent owner) (memories owner) (supported owner)
      saved savedMember (by simpa only [sameEvent] using physicalUnfinished)
    rw [sameEvent] at pendingReady
    exact ordered.ready_actor_unique execution.application.config.cut ready pendingReady
      actor completionActor

end Vegas.EventGraphRuntime
