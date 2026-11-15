module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.SchedulerReplay
public import Vegas.EventGraph.ObservationStep
public import Vegas.EventGraph.PrefixPolicy

@[expose] public section

/-! # Replaying a public scheduler at a source-prefix decision

The next selected event identifies the stopping point in a deterministic public
scheduler's transcript. At a binding decision, the source-prefix observation
therefore recovers the actual chronological observation when private binding
completions have introduced no default markers. The initial inputs may be
arbitrarily correlated.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A prefix's default entries can be read from the immutable records of its extension. -/
theorem path_history_map_defaults {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) :
    before.history.map EventCompletion.defaultEvent =
      (before.history.map EventCompletion.event).map fun event =>
        (completionOf after event).bind EventCompletion.defaultEvent := by
  rw [List.map_map]
  apply List.map_congr_left
  intro completion member
  have later : completion ∈ after.history := (Config.Step.path_history_prefix path).subset member
  rw [Function.comp_apply,
    (completionOf_eq_some_iff after completion.event completion).mpr ⟨later, rfl⟩]
  rfl

/-- Equal chronological prefixes have equal public observations when their endpoint public
stores and per-event default entries agree. The endpoint completed sets need not agree. -/
theorem publicObserve_eq_of_path_events_eq {left right middle other : graph.Config}
    (leftPath : Relation.ReflTransGen Config.Step middle left)
    (rightPath : Relation.ReflTransGen Config.Step other right)
    (events : middle.history.map EventCompletion.event = other.history.map EventCompletion.event)
    (publicSame : graph.publicStore left.store = graph.publicStore right.store)
    (defaultsSame : ∀ event, (completionOf left event).bind EventCompletion.defaultEvent =
      (completionOf right event).bind EventCompletion.defaultEvent) :
    graph.publicObserve middle = graph.publicObserve other := by
  have cuts := cut_eq_of_completionOrder_eq middle other events
  have stores : graph.publicStore middle.store = graph.publicStore other.store := by
    funext field
    cases field with
    | inl input =>
      have middleInputs := Config.Step.path_inputs_eq leftPath
      have otherInputs := Config.Step.path_inputs_eq rightPath
      have same := congrFun publicSame (.inl input)
      simp only [publicStore, Config.store_input, ← middleInputs, ← otherInputs] at same ⊢
      exact same
    | inr event =>
      by_cases done : event ∈ middle.cut.completed
      · have otherDone : event ∈ other.cut.completed := cuts ▸ done
        have same := congrFun publicSame (.inr event)
        simp only [publicStore, Config.store_output, path_outputs_of_completed leftPath done,
          path_outputs_of_completed rightPath otherDone] at same ⊢
        exact same
      · have otherPending : event ∉ other.cut.completed := cuts ▸ done
        have middleNone : middle.outputs event = none :=
          Option.not_isSome_iff_eq_none.mp fun present => done ((middle.output_available event).mp
            present)
        have otherNone : other.outputs event = none :=
          Option.not_isSome_iff_eq_none.mp fun present =>
            otherPending ((other.output_available event).mp present)
        simp only [publicStore, Config.store_output, middleNone, otherNone]
  have defaults : middle.defaults = other.defaults := by
    change EventCompletion.defaults middle.history = EventCompletion.defaults other.history
    simp only [EventCompletion.defaults]
    rw [path_history_map_defaults leftPath, path_history_map_defaults rightPath, events]
    exact congrArg (fun entries => DefaultHistory.mk entries.reverse)
      (List.map_congr_left fun event _ => defaultsSame event)
  exact EventPublicObservation.ext events stores defaults

omit [DecidableEq Player] in
open Classical in
/-- An assigned scheduler makes the same selection at equal public observations. -/
theorem assignedSelection_eq_of_publicObserve_eq
    (assignment : graph.ScheduleSite → Option graph.EventId) {left right : graph.Config}
    (leftActive : ¬ left.cut.Terminal) (rightActive : ¬ right.cut.Terminal)
    (same : graph.publicObserve left = graph.publicObserve right) :
    assignedSelection assignment left leftActive =
      assignedSelection assignment right rightActive := by
  have events := congrArg EventPublicObservation.completionOrder same
  have cuts := cut_eq_of_completionOrder_eq left right events
  have sites : scheduleSite left = scheduleSite right := by
    unfold scheduleSite
    rw [cuts, same]
  unfold assignedSelection
  have selectCongr : ∀ (enabled enabled' : Finset graph.EventId) (same : enabled = enabled')
      (nonempty : enabled.Nonempty) (nonempty' : enabled'.Nonempty)
      (drawn drawn' : Option graph.EventId), drawn = drawn' →
      (selectAt enabled nonempty drawn).1 = (selectAt enabled' nonempty' drawn').1 := by
    intro enabled enabled' same nonempty nonempty' drawn drawn' sameDrawn
    subst same sameDrawn
    rfl
  exact selectCongr _ _ (by rw [cuts]) _ _ _ _ (by rw [sites])

/-- A common next selection fixes the entire completed chronological transcript even when the
completed sets are initially unknown. This is a stopping-time form of deterministic replay. -/
theorem assigned_history_events_eq_of_same_next {profile : graph.BehavioralProfile}
    {assignment : graph.ScheduleSite → Option graph.EventId} {first second : graph.Inputs}
    {left right : graph.Config} {event : graph.EventId}
    (leftReach : PlanReachable profile (assignedScheduler assignment) (Config.initial first) left)
    (rightReach : PlanReachable profile (assignedScheduler assignment) (Config.initial second)
      right)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftSelected : assignedSelection assignment left leftReady.not_terminal = event)
    (rightSelected : assignedSelection assignment right rightReady.not_terminal = event)
    (publicSame : graph.publicStore left.store = graph.publicStore right.store)
    (defaultsSame : ∀ prior, (completionOf left prior).bind EventCompletion.defaultEvent =
      (completionOf right prior).bind EventCompletion.defaultEvent) :
    left.history.map EventCompletion.event = right.history.map EventCompletion.event := by
  have prefixes : ∀ length, length ≤ left.history.length → length ≤ right.history.length →
      (left.history.map EventCompletion.event).take length =
        (right.history.map EventCompletion.event).take length := by
    intro length
    induction length with
    | zero => intro _ _; simp
    | succ length ih =>
      intro leftBound rightBound
      have earlier := ih (by omega) (by omega)
      obtain ⟨middle, _, leftRest, middleLength⟩ :=
        leftReach.exists_middle length (by simp [Config.initial]) (by omega)
      obtain ⟨other, _, rightRest, otherLength⟩ :=
        rightReach.exists_middle length (by simp [Config.initial]) (by omega)
      have middleHistory : middle.history = left.history.take length := by
        have kept := Config.Step.path_history_prefix (PlanReachable.toPath leftRest)
        rw [List.prefix_iff_eq_take] at kept
        rw [kept, middleLength]
      have otherHistory : other.history = right.history.take length := by
        have kept := Config.Step.path_history_prefix (PlanReachable.toPath rightRest)
        rw [List.prefix_iff_eq_take] at kept
        rw [kept, otherLength]
      have events : middle.history.map EventCompletion.event =
          other.history.map EventCompletion.event := by
        rw [middleHistory, otherHistory, List.map_take, List.map_take, earlier]
      have publicEq := publicObserve_eq_of_path_events_eq leftRest.toPath rightRest.toPath events
        publicSame defaultsSame
      obtain ⟨middleActive, leftEvent⟩ := leftRest.next_event (by omega)
      obtain ⟨otherActive, rightEvent⟩ := rightRest.next_event (by omega)
      have selections := assignedSelection_eq_of_publicObserve_eq assignment middleActive
        otherActive publicEq
      rw [List.take_add_one, List.take_add_one, earlier]
      congr 1
      simp only [List.getElem?_map]
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some]
      simp only [middleLength] at leftEvent
      simp only [otherLength] at rightEvent
      rw [leftEvent, rightEvent, selections]
  have cannotShorter {a b : graph.Config} {aInput bInput : graph.Inputs}
      (_aReach : PlanReachable profile (assignedScheduler assignment) (Config.initial aInput) a)
      (bReach : PlanReachable profile (assignedScheduler assignment) (Config.initial bInput) b)
      (aReady : a.cut.Ready event) (bReady : b.cut.Ready event)
      (selected : assignedSelection assignment a aReady.not_terminal = event)
      (stores : graph.publicStore a.store = graph.publicStore b.store)
      (records : ∀ prior, (completionOf a prior).bind EventCompletion.defaultEvent =
        (completionOf b prior).bind EventCompletion.defaultEvent)
      (samePrefix : (a.history.map EventCompletion.event).take a.history.length =
        (b.history.map EventCompletion.event).take a.history.length) :
      ¬ a.history.length < b.history.length := by
    intro shorter
    obtain ⟨middle, _, rest, middleLength⟩ :=
      bReach.exists_middle a.history.length (by simp [Config.initial]) shorter.le
    have middleHistory : middle.history = b.history.take a.history.length := by
      have kept := Config.Step.path_history_prefix rest.toPath
      rw [List.prefix_iff_eq_take] at kept
      rw [kept, middleLength]
    have events : a.history.map EventCompletion.event =
        middle.history.map EventCompletion.event := by
      rw [middleHistory, List.map_take, ← samePrefix]
      exact (List.take_of_length_le (by simp)).symm
    have publicEq := publicObserve_eq_of_path_events_eq Relation.ReflTransGen.refl rest.toPath
      events stores records
    obtain ⟨active, next⟩ := rest.next_event (by omega)
    have selection := assignedSelection_eq_of_publicObserve_eq assignment aReady.not_terminal
      active publicEq
    have eventMem : event ∈ b.history.map EventCompletion.event := by
      have sameEvent : (b.history[a.history.length]'shorter).event = event := by
        have next' : (b.history[a.history.length]'shorter).event =
            assignedSelection assignment middle active := by
          simpa only [middleLength] using next
        exact next'.trans (selection.symm.trans selected)
      exact List.mem_map.mpr ⟨_, List.getElem_mem shorter, sameEvent⟩
    exact bReady.1 ((b.history_exact event).mp eventMem)
  have leftLe : left.history.length ≤ right.history.length := by
    by_contra notLe
    have shorter : right.history.length < left.history.length := Nat.lt_of_not_ge notLe
    exact cannotShorter rightReach leftReach rightReady leftReady rightSelected publicSame.symm
      (fun prior => (defaultsSame prior).symm)
      (prefixes right.history.length shorter.le le_rfl).symm shorter
  have rightLe : right.history.length ≤ left.history.length := by
    by_contra notLe
    have shorter : left.history.length < right.history.length := Nat.lt_of_not_ge notLe
    exact cannotShorter leftReach rightReach leftReady rightReady leftSelected publicSame
      defaultsSame (prefixes left.history.length le_rfl shorter.le) shorter
  have whole := prefixes left.history.length le_rfl leftLe
  have leftTake : (left.history.map EventCompletion.event).take left.history.length =
      left.history.map EventCompletion.event := List.take_of_length_le (by simp)
  have rightTake : (right.history.map EventCompletion.event).take left.history.length =
      right.history.map EventCompletion.event :=
    List.take_of_length_le (by simpa only [List.length_map] using rightLe)
  exact leftTake.symm.trans (whole.trans rightTake)

/-- At a ready nonpublication every normalized own completion is source-ranked before it. -/
theorem normalizedOwnActions_before_ready (relaxed : graph.RevealRelaxedOrdered)
    (who : Player) (event : graph.EventId) (config : graph.Config)
    (ready : config.cut.Ready event) (actor : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication) :
    ((graph.normalizeObservation who (graph.playerObserve who config)).ownActions.filter
      (fun completion => completion.event.val < event.val)) =
    (graph.normalizeObservation who (graph.playerObserve who config)).ownActions := by
  apply List.filter_eq_self.mpr
  intro completion member
  rw [normalizeObservation_playerObserve] at member
  obtain ⟨prior, _inside, found⟩ := List.mem_filterMap.mp member
  obtain ⟨found, owned⟩ := Option.filter_eq_some_iff.mp found
  simp only [decide_eq_true_eq] at owned
  have actual := (completionOf_eq_some_iff config prior completion).mp found
  have completed : completion.event ∈ config.cut.completed :=
    (config.history_exact completion.event).mp
      (List.mem_map.mpr ⟨completion, actual.1, rfl⟩)
  have before := (relaxed.ready_visible_iff config.cut ready actor
    (EventCode.output_visible_of_actor (graph.nodes completion.event) who owned.1)
    (IndependentReveals.not_of_not_publication_right notPublication)
    (IndependentReveals.not_of_not_publication_left notPublication)).mp completed
  simpa only [decide_eq_true_eq] using before

/-- A ready binding selected next by one assigned scheduler has its actual observation uniquely
determined by its source-prefix observation, when private completions record no public default. -/
theorem assigned_playerObserve_eq_of_prefix {profile : graph.BehavioralProfile}
    {assignment : graph.ScheduleSite → Option graph.EventId} {first second : graph.Inputs}
    {left right : graph.Config}
    (leftReach : PlanReachable profile (assignedScheduler assignment) (Config.initial first) left)
    (rightReach : PlanReachable profile (assignedScheduler assignment) (Config.initial second)
      right)
    (relaxed : graph.RevealRelaxedOrdered) (who : Player) (event : graph.EventId)
    (actor : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftSelected : assignedSelection assignment left leftReady.not_terminal = event)
    (rightSelected : assignedSelection assignment right rightReady.not_terminal = event)
    (leftPrivate : ∀ prior, ¬ (graph.outputLayout prior).IsPublic →
      (completionOf left prior).bind EventCompletion.defaultEvent = none)
    (rightPrivate : ∀ prior, ¬ (graph.outputLayout prior).IsPublic →
      (completionOf right prior).bind EventCompletion.defaultEvent = none)
    (same : graph.prefixObservation who event (graph.playerObserve who left) =
      graph.prefixObservation who event (graph.playerObserve who right)) :
    graph.playerObserve who left = graph.playerObserve who right := by
  have stores := congrArg EventPlayerObservation.store same
  change graph.playerStore who left.store = graph.playerStore who right.store at stores
  have publicSame : graph.publicStore left.store = graph.publicStore right.store := by
    rw [← publicStore_playerStore who left.store, ← publicStore_playerStore who right.store]
    exact congrArg graph.publicStore stores
  have prefixDefaults := congrArg (fun observation => observation.defaults.events.reverse) same
  simp only [prefixObservation, List.reverse_reverse] at prefixDefaults
  have records : ∀ prior, (completionOf left prior).bind EventCompletion.defaultEvent =
      (completionOf right prior).bind EventCompletion.defaultEvent := by
    intro prior
    by_cases isPublic : (graph.outputLayout prior).IsPublic
    · by_cases earlier : prior.val < event.val
      · have member : prior ∈ graph.decisionPrefix event := by
          simp only [decisionPrefix, List.mem_filter, List.mem_finRange, decide_eq_true_eq,
            true_and]
          exact earlier
        have sameMarker := List.map_inj_left.mp prefixDefaults prior member
        simpa only [ite_eq_left isPublic, observedDefaultOf_playerObserve] using sameMarker
      · have absent (config : graph.Config) (ready : config.cut.Ready event) :
            completionOf config prior = none := by
          have notCompleted : prior ∉ config.cut.completed := by
            intro completed
            exact earlier ((relaxed.ready_visible_iff config.cut ready actor
              (by cases layout : graph.outputLayout prior <;> simp_all [EventField.IsPublic,
                EventField.VisibleTo])
              (IndependentReveals.not_of_not_publication_right notPublication)
              (IndependentReveals.not_of_not_publication_left notPublication)).mp completed)
          exact Option.not_isSome_iff_eq_none.mp fun present =>
            notCompleted ((mem_completed_iff_completionOf config prior).mpr present)
        rw [absent left leftReady, absent right rightReady]
    · rw [leftPrivate prior isPublic, rightPrivate prior isPublic]
  have events := assigned_history_events_eq_of_same_next leftReach rightReach leftReady rightReady
    leftSelected rightSelected publicSame records
  have completed : ∀ prior, (completionOf left prior).isSome =
      (completionOf right prior).isSome := by
    intro prior
    apply Bool.eq_iff_iff.mpr
    rw [← mem_completed_iff_completionOf, ← mem_completed_iff_completionOf]
    exact Iff.of_eq (congrArg (fun events => prior ∈ events)
      (congrArg EventOrder.Cut.completed (cut_eq_of_completionOrder_eq left right events)))
  have sorted : (List.finRange graph.order.eventCount).filter
        (fun prior => (completionOf left prior).isSome) =
      (List.finRange graph.order.eventCount).filter
        (fun prior => (completionOf right prior).isSome) :=
    List.filter_congr fun prior _ => completed prior
  have owns := congrArg EventPlayerObservation.ownActions same
  change ((graph.normalizeObservation who (graph.playerObserve who left)).ownActions.filter
      (fun completion => completion.event.val < event.val)) =
    ((graph.normalizeObservation who (graph.playerObserve who right)).ownActions.filter
      (fun completion => completion.event.val < event.val)) at owns
  rw [normalizedOwnActions_before_ready relaxed who event left leftReady actor notPublication,
    normalizedOwnActions_before_ready relaxed who event right rightReady actor notPublication]
    at owns
  apply assigned_playerObserve_eq leftReach rightReach who
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve]
  apply EventPlayerObservation.ext
  · exact sorted
  · exact stores
  · simpa only [normalizeObservation_playerObserve] using owns
  · rw [sorted]
    exact congrArg (fun entries => DefaultHistory.mk entries.reverse)
      (List.map_congr_left fun prior _ => records prior)

end Vegas.EventGraph
