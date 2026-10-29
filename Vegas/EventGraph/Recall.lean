/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

/-- Active owners have a genuine decision at every completed owned event. -/
theorem Config.Reachable.owned_decision_isSome_of_active
    {inputs : graph.Inputs} {config : graph.Config}
    (reachable : Config.Reachable inputs config) (who : Player)
    (active : who ∉ config.defaulted) :
    ∀ completion ∈ config.history, graph.actor? completion.event = some who →
      completion.decision.isSome := by
  induction reachable with
  | initial => simp [Config.initial]
  | @step prior reachable event ready action next supported ih =>
      have priorActive : who ∉ prior.defaulted :=
        fun excluded => active (prior.defaulted_step event ready action next supported excluded)
      obtain ⟨value, _, history⟩ := prior.step_completion event ready action next supported
      rw [history]
      intro completion member owned
      rcases List.mem_append.mp member with old | new
      · exact ih priorActive completion old owned
      · have same : completion = Completion.fromDecision event
            (prior.actualDecision event action) value := by simpa using new
        subst completion
        change graph.actor? event = some who at owned
        change (graph.nodes event).actor = some who at owned
        change (prior.actualDecision event action).isSome
        simp only [Config.actualDecision, EventCode.actualDecision, owned, priorActive,
          ↓reduceIte, Option.isSome_some]

/-- Every recorded public default belongs to the event's actual owner. -/
theorem Config.Reachable.defaultEvent_actor
    {inputs : graph.Inputs} {config : graph.Config}
    (reachable : Config.Reachable inputs config) :
    ∀ completion ∈ config.history, ∀ who, completion.defaultEvent = some who →
      graph.actor? completion.event = some who := by
  induction reachable with
  | initial => simp [Config.initial]
  | @step prior reachable event ready action next supported ih =>
      obtain ⟨value, _, history⟩ := prior.step_completion event ready action next supported
      rw [history]
      intro completion member who defaulted
      rcases List.mem_append.mp member with old | new
      · exact ih completion old who defaulted
      · have same : completion = Completion.fromDecision event
            (prior.actualDecision event action) value := by simpa using new
        subst completion
        change ((prior.actualDecision event action).bind fun chosen =>
          (graph.nodes event).defaultEvent chosen value) = some who at defaulted
        cases decision : prior.actualDecision event action with
        | none => simp [decision] at defaulted
        | some choice =>
            simp only [decision, Option.bind_some, EventCode.defaultEvent] at defaulted
            split at defaulted
            · exact defaulted
            · cases defaulted

/-- An active owner's completed events never announced its public default. -/
theorem Config.Reachable.owned_defaultEvent_eq_none_of_active
    {inputs : graph.Inputs} {config : graph.Config}
    (reachable : Config.Reachable inputs config) (who : Player)
    (active : who ∉ config.defaulted)
    (completion : graph.Completion) (member : completion ∈ config.history)
    (owned : graph.actor? completion.event = some who) : completion.defaultEvent = none := by
  cases flag : completion.defaultEvent with
  | none => rfl
  | some owner =>
      have same : owner = who := Option.some.inj
        ((reachable.defaultEvent_actor completion member owner flag).symm.trans owned)
      subst owner
      apply (active ?_).elim
      change who ∈ ((config.history.map Completion.defaultEvent).reverse.filterMap id).toFinset
      simp only [List.mem_toFinset, List.mem_filterMap, List.mem_reverse, List.mem_map]
      exact ⟨some who, ⟨completion, member, flag⟩, rfl⟩

/-- Completed actual choices of an owner follow increasing graph rank. -/
theorem Config.Reachable.ownEventIds_pairwise
    {inputs : graph.Inputs} {config : graph.Config}
    (reachable : Config.Reachable inputs config)
    (discipline : graph.InformationDiscipline schema) (who : Player) :
    (graph.ownEventIds who config.history).Pairwise fun left right =>
      left.val < right.val := by
  induction reachable with
  | initial => simp [ownEventIds, ownCompletions, Config.initial]
  | @step prior priorReachable event ready action next supported ih =>
      obtain ⟨value, _, history⟩ := prior.step_completion event ready action next supported
      rw [history, ownEventIds, ownCompletions, List.filter_append]
      simp only [List.filter_cons, List.filter_nil]
      split
      · rename_i owned
        have owner : graph.actor? event = some who := (of_decide_eq_true owned).1
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
          (of_decide_eq_true filtered.2).1
        by_contra notEarlier
        have different : event ≠ completion.event := by
          intro same
          subst event
          exact ready.1 earlierCompleted
        have later : event.val < completion.event.val := by
          exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt notEarlier)
            (fun equal => different (Fin.ext equal))
        have predecessor : event ∈ graph.order.predecessors completion.event :=
          discipline.same_owner_ordered later owner earlierOwned
        exact ready.1 (prior.cut.predecessor_closed earlierCompleted predecessor)
      · simp only [List.map_append, List.map_nil]
        change (graph.ownEventIds who prior.history ++ []).Pairwise _
        simpa using ih

/-- An active actor's past choices are exactly its declared source-ranked history. -/
theorem InformationDiscipline.ready_ownEventIds
    (discipline : graph.InformationDiscipline schema)
    {inputs : graph.Inputs} {config : graph.Config}
    (reachable : Config.Reachable inputs config) {event : graph.EventId}
    {who : Player} (ready : config.cut.Ready event)
    (actor : graph.actor? event = some who) (active : who ∉ config.defaulted) :
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
        (List.mem_map.mpr ⟨completion, inHistory, rfl⟩), (of_decide_eq_true owned).1⟩
    · rintro ⟨completed, owned⟩
      obtain ⟨completion, inHistory, eventEq⟩ :=
        List.mem_map.mp ((config.history_exact candidate).mpr completed)
      have completionOwned : graph.actor? completion.event = some who := eventEq.symm ▸ owned
      exact ⟨completion, ⟨inHistory, by
        simp only [decide_eq_true_eq]
        exact ⟨completionOwned,
          reachable.owned_decision_isSome_of_active who active completion
            inHistory completionOwned⟩⟩,
        eventEq⟩
  have declaredSet := discipline.ready_own_history_exact config.cut event who ready actor
  have setsEqual : (graph.ownEventIds who config.history).toFinset =
      (schema.ownHistory event).toFinset := actualSet.trans declaredSet.symm
  simpa only [List.mem_toFinset] using
    Iff.of_eq (congrArg (fun (set : Finset graph.EventId) => prior ∈ set) setsEqual)

end Vegas.EventGraph
