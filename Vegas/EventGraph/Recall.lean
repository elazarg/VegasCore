/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Information

/-! # Source-ranked recall in reachable event-graph executions

Information discipline orders one player's strategic events by graph rank.
Reachability turns that dependency order into chronological recall while
retaining the original dependent actions in the completion records.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L} {schema : graph.LogicalSchema}

/-- Event identities in one player's chronological completion history. -/
def ownEventIds (graph : Vegas.EventGraph Player L) (who : Player)
    (history : List graph.Completion) : List graph.EventId :=
  (graph.ownCompletions who history).map Completion.event

/-- In a reachable execution, one player's completed strategic events occur
in strictly increasing graph rank. The underlying completion records still
retain their original dependent actions. -/
theorem Config.Reachable.ownEventIds_pairwise
    {inputs : graph.Inputs} {config : graph.Config}
    (reachable : Config.Reachable inputs config)
    (discipline : graph.InformationDiscipline schema) (who : Player) :
    (graph.ownEventIds who config.history).Pairwise fun left right =>
      left.val < right.val := by
  induction reachable with
  | initial => simp [ownEventIds, ownCompletions, Config.initial]
  | step priorReachable event ready action next supported ih =>
      rename_i prior
      rw [Config.step_history prior event ready action next supported]
      rw [ownEventIds, ownCompletions, List.filter_append]
      simp only [List.filter_cons, List.filter_nil]
      split
      · rename_i owned
        simp only [List.map_append, List.map_cons, List.map_nil]
        change (graph.ownEventIds who prior.history ++ [event]).Pairwise _
        rw [List.pairwise_append]
        refine ⟨ih, by simp, ?_⟩
        intro earlier earlierMem later laterMem
        have : later = event := by simpa using laterMem
        subst later
        have completionMem : ∃ completion ∈ graph.ownCompletions who prior.history,
            completion.event = earlier := by
          simpa [ownEventIds] using earlierMem
        obtain ⟨completion, completionOwn, rfl⟩ := completionMem
        have filtered := List.mem_filter.mp completionOwn
        have earlierCompleted : completion.event ∈ prior.cut.completed := by
          apply (prior.history_exact completion.event).mp
          exact List.mem_map.mpr ⟨completion, filtered.1, rfl⟩
        have earlierOwned : graph.actor? completion.event = some who :=
          of_decide_eq_true filtered.2
        by_contra notEarlier
        have different : event ≠ completion.event := by
          intro same
          subst event
          exact ready.1 earlierCompleted
        have later : event.val < completion.event.val := by
          exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt notEarlier)
            (fun equal => different (Fin.ext equal))
        have predecessor : event ∈ graph.order.predecessors completion.event :=
          discipline.same_owner_ordered later (of_decide_eq_true owned) earlierOwned
        exact ready.1 (prior.cut.predecessor_closed earlierCompleted predecessor)
      · simp only [List.map_append, List.map_nil]
        change (graph.ownEventIds who prior.history ++ []).Pairwise _
        simpa using ih

/-- At a ready strategic event, the chronologically retained identities of
the actor's original actions are exactly the source-ranked history declared by
the logical schema. This compares identities only; the completion records keep
the dependent actions themselves. -/
theorem InformationDiscipline.ready_ownEventIds
    (discipline : graph.InformationDiscipline schema)
    {inputs : graph.Inputs} {config : graph.Config}
    (reachable : Config.Reachable inputs config) {event : graph.EventId}
    {who : Player} (ready : config.cut.Ready event)
    (actor : graph.actor? event = some who) :
    graph.ownEventIds who config.history = schema.ownHistory event := by
  apply (reachable.ownEventIds_pairwise discipline who).eq_of_mem_iff
    (discipline.own_history_ranked event)
  intro prior
  have actualSet : (graph.ownEventIds who config.history).toFinset =
      graph.completedOwnEvents who config.cut := by
    ext candidate
    simp only [ownEventIds, ownCompletions, List.mem_toFinset, List.mem_map,
      List.mem_filter, completedOwnEvents, Finset.mem_filter]
    constructor
    · rintro ⟨completion, ⟨inHistory, owned⟩, rfl⟩
      exact ⟨(config.history_exact completion.event).mp
        (List.mem_map.mpr ⟨completion, inHistory, rfl⟩), of_decide_eq_true owned⟩
    · rintro ⟨completed, owned⟩
      obtain ⟨completion, inHistory, eventEq⟩ :=
        List.mem_map.mp ((config.history_exact candidate).mpr completed)
      exact ⟨completion, ⟨inHistory, by simp [eventEq, owned]⟩, eventEq⟩
  have declaredSet :=
    discipline.ready_own_history_exact config.cut event who ready actor
  have setsEqual : (graph.ownEventIds who config.history).toFinset =
      (schema.ownHistory event).toFinset := actualSet.trans declaredSet.symm
  simpa only [List.mem_toFinset] using
    Iff.of_eq (congrArg (fun (set : Finset graph.EventId) => prior ∈ set) setsEqual)

end Vegas.EventGraph
