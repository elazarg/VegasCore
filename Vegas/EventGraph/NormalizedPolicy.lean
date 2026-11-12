module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.CommutationRecall
public import Vegas.EventGraph.Semantics

@[expose] public section

/-! # Rank-normalized event-graph policies

A normalized policy sees its actual observation with every chronological list
rearranged into the graph's fixed event rank: the completion order, the default
entry recorded for each completed event, and the player's own completions. The
projected store is unchanged. A normalized policy therefore cannot react to the
order in which a scheduler completed simultaneously ready events, and under the
canonical scheduler, which completes events in rank order, normalization
changes no observation.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

variable (graph : Vegas.EventGraph Player L)

/-- The events of a list, in the graph's fixed rank, without repetition. -/
def rankSort (events : List graph.EventId) : List graph.EventId :=
  (List.finRange graph.order.eventCount).filter fun event => event ∈ events

/-- The default entry an observation records for one completed event: the
chronological completion order paired with the chronological default log. -/
def observedDefaultOf {who : Player} (observation : graph.PlayerObservation who)
    (event : graph.EventId) : Option Player :=
  ((observation.completionOrder.zip observation.defaults.events.reverse).find?
    fun entry => entry.1 = event).bind Prod.snd

/-- Rearrange an observation's chronological lists into rank order. -/
def normalizeObservation (who : Player) (observation : graph.PlayerObservation who) :
    graph.PlayerObservation who where
  completionOrder := graph.rankSort observation.completionOrder
  store := observation.store
  ownActions := (List.finRange graph.order.eventCount).filterMap fun event =>
    observation.ownActions.find? fun completion => completion.event = event
  defaults := ⟨((graph.rankSort observation.completionOrder).map
    (graph.observedDefaultOf observation)).reverse⟩

/-- Normalization reports no default the observation does not already report. -/
theorem normalizeObservation_defaulted_subset (who : Player)
    (observation : graph.PlayerObservation who) :
    (graph.normalizeObservation who observation).defaulted ⊆ observation.defaulted := by
  intro owner member
  simp only [EventPlayerObservation.defaulted, DefaultHistory.defaulted, normalizeObservation,
    List.mem_toFinset, List.mem_filterMap, List.mem_reverse, List.mem_map, id_eq] at member ⊢
  obtain ⟨_, ⟨event, _, found⟩, rfl⟩ := member
  simp only [observedDefaultOf, Option.bind_eq_some_iff] at found
  obtain ⟨entry, entryFound, entryDefault⟩ := found
  have entryMember := List.mem_of_find?_eq_some entryFound
  have := (List.of_mem_zip entryMember).2
  exact ⟨entry.2, by rwa [List.mem_reverse] at this, entryDefault⟩

/-- Compile a policy to read only its rank-normalized observation. -/
def normalizePolicy (who : Player) (policy : graph.BehavioralPolicy who) :
    graph.BehavioralPolicy who :=
  fun event actor observation active =>
    policy event actor (graph.normalizeObservation who observation)
      (fun normalized => active (graph.normalizeObservation_defaulted_subset who observation
        normalized))

/-- Normalize every player policy independently. -/
def normalizeProfile (profile : graph.BehavioralProfile) : graph.BehavioralProfile :=
  fun who => graph.normalizePolicy who (profile who)

/-- Normalization acts independently on each player's policy. -/
theorem normalizeProfile_update (profile : graph.BehavioralProfile)
    (who : Player) (replacement : graph.BehavioralPolicy who) :
    graph.normalizeProfile
        (GameTheory.Profile.update (sig := graph.gameSignature) profile who replacement) =
      GameTheory.Profile.update (sig := graph.gameSignature)
        (graph.normalizeProfile profile) who (graph.normalizePolicy who replacement) := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [normalizeProfile, GameTheory.Profile.update_same]
  · simp only [normalizeProfile, GameTheory.Profile.update_of_ne _ _ same]

section Actual

variable {graph}

omit [DecidableEq Player] in
theorem find?_filter_of_nodup (history : List graph.Completion)
    (nodup : (history.map EventCompletion.event).Nodup) (keep : graph.Completion → Bool)
    (event : graph.EventId) :
    (history.filter keep).find? (fun completion => completion.event = event) =
      (history.find? fun completion => completion.event = event).filter keep := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at nodup
      obtain ⟨headFresh, tailNodup⟩ := nodup
      by_cases hit : head.event = event
      · have tailMiss : tail.find? (fun completion => completion.event = event) = none := by
          rw [List.find?_eq_none]
          intro other member otherHit
          exact headFresh ⟨other, member, by simpa [hit] using otherHit⟩
        cases kept : keep head
        · simp [kept, hit, ih tailNodup, tailMiss, Option.filter]
        · simp [kept, hit, Option.filter]
      · cases kept : keep head <;> simp [kept, hit, ih tailNodup]

omit [DecidableEq Player] in
theorem find?_zip_map (history : List graph.Completion) (event : graph.EventId) :
    ((history.map EventCompletion.event).zip (history.map EventCompletion.defaultEvent)).find?
        (fun entry => entry.1 = event) =
      (history.find? fun completion => completion.event = event).map
        fun completion => (completion.event, completion.defaultEvent) := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
      by_cases hit : head.event = event <;> simp [hit, ih]

/-- The normalized observation of an actual configuration, read from the store
and the completion recorded for each event. -/
theorem normalizeObservation_playerObserve (who : Player) (config : graph.Config) :
    graph.normalizeObservation who (graph.playerObserve who config) =
      { completionOrder := (List.finRange graph.order.eventCount).filter fun event =>
          (completionOf config event).isSome
        store := graph.playerStore who config.store
        ownActions := (List.finRange graph.order.eventCount).filterMap fun event =>
          (completionOf config event).filter fun completion =>
            graph.actor? completion.event = some who ∧ completion.decision.isSome
        defaults := ⟨(((List.finRange graph.order.eventCount).filter fun event =>
          (completionOf config event).isSome).map fun event =>
            (completionOf config event).bind EventCompletion.defaultEvent).reverse⟩ } := by
  have member (event : graph.EventId) :
      decide (event ∈ config.history.map EventCompletion.event) =
        (completionOf config event).isSome := by
    unfold completionOf
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.find?_isSome]
    simp [List.mem_map]
  have sorted : graph.rankSort (config.history.map EventCompletion.event) =
      (List.finRange graph.order.eventCount).filter fun event =>
        (completionOf config event).isSome := by
    unfold rankSort
    exact List.filter_congr fun event _ => member event
  have defaultOf (event : graph.EventId) :
      graph.observedDefaultOf (graph.playerObserve who config) event =
        (completionOf config event).bind EventCompletion.defaultEvent := by
    unfold observedDefaultOf
    change (((config.history.map EventCompletion.event).zip
      (EventCompletion.defaults config.history).events.reverse).find? _).bind _ = _
    simp only [EventCompletion.defaults, List.reverse_reverse]
    rw [find?_zip_map]
    unfold completionOf
    cases config.history.find? (fun completion => completion.event = event) <;> rfl
  apply EventPlayerObservation.ext
  · exact sorted
  · rfl
  · change List.filterMap _ _ = _
    congr 1
    funext event
    change (graph.ownCompletions who config.history).find? _ = _
    unfold ownCompletions
    rw [find?_filter_of_nodup config.history config.history_nodup]
    rfl
  · change DefaultHistory.mk ((List.map (graph.observedDefaultOf (graph.playerObserve who config))
      (graph.rankSort (config.history.map EventCompletion.event))).reverse) = _
    rw [sorted]
    congr 2
    exact List.map_congr_left fun event _ => defaultOf event

/-- Two configurations with the same store and completion records give every
player the same normalized observation. -/
theorem normalizeObservation_playerObserve_congr (who : Player) {left right : graph.Config}
    (same : graph.storeRecall left = graph.storeRecall right) :
    graph.normalizeObservation who (graph.playerObserve who left) =
      graph.normalizeObservation who (graph.playerObserve who right) := by
  have store : left.store = right.store := congrArg Prod.fst same
  have records : completionOf left = completionOf right := congrArg Prod.snd same
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve, store, records]

omit [DecidableEq Player] in
/-- Looking up each event of a history without repeated events returns its own completion. -/
private theorem map_find?_events (history : List graph.Completion)
    (nodup : (history.map EventCompletion.event).Nodup) :
    (history.map EventCompletion.event).map
        (fun event => history.find? fun completion => completion.event = event) =
      history.map some := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at nodup ⊢
      obtain ⟨headFresh, tailNodup⟩ := nodup
      refine congrArg₂ List.cons (by simp) ?_
      rw [← ih tailNodup]
      apply List.map_congr_left
      intro event member
      obtain ⟨completion, inTail, rfl⟩ := List.mem_map.mp member
      have different : ¬ head.event = completion.event := fun same =>
        headFresh ⟨completion, inTail, same.symm⟩
      simp [different]

omit [DecidableEq Player] in
private theorem filterMap_ite_eq_filter {α : Type} (keep : α → Prop) [DecidablePred keep]
    (items : List α) :
    items.filterMap (fun item => if keep item then some item else none) =
      items.filter fun item => decide (keep item) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      by_cases kept : keep head <;> simp [kept, ih]

/-- A configuration whose history lists its events in rank order is observed
identically before and after normalization. -/
theorem normalizeObservation_playerObserve_of_rankOrdered (who : Player) (config : graph.Config)
    (ordered : graph.rankSort (config.history.map EventCompletion.event) =
      config.history.map EventCompletion.event) :
    graph.normalizeObservation who (graph.playerObserve who config) =
      graph.playerObserve who config := by
  have sortedRecords : ((List.finRange graph.order.eventCount).filter fun event =>
      (completionOf config event).isSome) = config.history.map EventCompletion.event := by
    rw [← ordered]
    unfold rankSort
    refine List.filter_congr fun event _ => ?_
    unfold completionOf
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.find?_isSome]
    simp [List.mem_map]
  have each : ∀ completion ∈ config.history,
      config.history.find? (fun other => other.event = completion.event) = some completion := by
    have lookup := map_find?_events config.history config.history_nodup
    rw [List.map_map] at lookup
    exact fun completion member => List.map_inj_left.mp lookup completion member
  have records (read : graph.Completion → Option graph.Completion) :
      (List.finRange graph.order.eventCount).filterMap
          (fun event => (completionOf config event).bind read) =
        config.history.filterMap read := by
    have restricted : (List.finRange graph.order.eventCount).filterMap
          (fun event => (completionOf config event).bind read) =
        ((List.finRange graph.order.eventCount).filter fun event =>
          (completionOf config event).isSome).filterMap
            (fun event => (completionOf config event).bind read) := by
      rw [List.filterMap_filter]
      congr 1
      funext event
      cases (completionOf config event) <;> rfl
    rw [restricted, sortedRecords, List.filterMap_map]
    refine List.filterMap_congr fun completion member => ?_
    simp [completionOf, each completion member]
  rw [normalizeObservation_playerObserve]
  apply EventPlayerObservation.ext
  · exact sortedRecords
  · rfl
  · dsimp only
    change _ = config.history.filter _
    have filtered := records fun completion =>
      if graph.actor? completion.event = some who ∧ completion.decision.isSome then some completion
      else none
    rw [filterMap_ite_eq_filter] at filtered
    rw [← filtered]
    congr 1
    funext event
    cases completionOf config event <;> simp [Option.filter]
  · change DefaultHistory.mk _ = DefaultHistory.mk _
    rw [sortedRecords, List.map_map]
    congr 2
    refine List.map_congr_left fun completion member => ?_
    simp [completionOf, each completion member]

end Actual

end Vegas.EventGraph
