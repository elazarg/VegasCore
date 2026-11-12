module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.SchedulerPredraw

@[expose] public section

/-! # Replaying a deterministic public scheduler

Under a deterministic public scheduler the order of completions is recomputed
from public data: at each prefix of a run the scheduler sees the events
completed so far, their public outputs and their default entries, and its
selection is a function of that view. Two configurations reachable under the
same deterministic scheduler, with the same completed events, the same public
outputs and the same default entries, therefore list their events in the same
order.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

theorem PlanStep.toStep {profile : graph.BehavioralProfile} {scheduler : graph.PublicScheduler}
    {before after : graph.Config} (step : PlanStep profile scheduler before after) :
    Config.Step before after := by
  obtain ⟨_, selected, _, member⟩ := step
  unfold eventStep at member
  rw [PMF.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨action, _, stepped⟩ := member
  exact ⟨selected.1, (EventOrder.Cut.mem_enabled _ _).mp selected.2, action, stepped⟩

theorem PlanReachable.toPath {profile : graph.BehavioralProfile}
    {scheduler : graph.PublicScheduler} {before after : graph.Config}
    (reach : PlanReachable profile scheduler before after) :
    Relation.ReflTransGen Config.Step before after := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail step.toStep

/-- Every prefix length of a reachable history is reached on the way. -/
theorem PlanReachable.exists_middle {profile : graph.BehavioralProfile}
    {scheduler : graph.PublicScheduler} {start last : graph.Config}
    (reach : PlanReachable profile scheduler start last) (length : Nat)
    (lower : start.history.length ≤ length) (upper : length ≤ last.history.length) :
    ∃ middle, PlanReachable profile scheduler start middle ∧
      PlanReachable profile scheduler middle last ∧ middle.history.length = length := by
  induction reach with
  | refl => exact ⟨start, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, by omega⟩
  | @tail before after earlier step ih =>
      by_cases within : length ≤ before.history.length
      · obtain ⟨middle, first, second, sized⟩ := ih within
        exact ⟨middle, first, second.tail step, sized⟩
      · have grown := step.history_length
        exact ⟨after, earlier.tail step, Relation.ReflTransGen.refl, by omega⟩

/-- The selection of a deterministic assigned scheduler at a configuration. -/
def assignedSelection (assignment : graph.ScheduleSite → Option graph.EventId)
    (config : graph.Config) (notTerminal : ¬ config.cut.Terminal) : graph.EventId :=
  (selectAt config.cut.enabled (enabled_nonempty_of_not_terminal config notTerminal)
    (assignment (scheduleSite config))).1

/-- Under an assigned scheduler, the event completed after a reachable middle
configuration is the scheduler's selection there. -/
theorem PlanReachable.next_event {profile : graph.BehavioralProfile}
    {assignment : graph.ScheduleSite → Option graph.EventId} {middle last : graph.Config}
    (reach : PlanReachable profile (assignedScheduler assignment) middle last)
    (shorter : middle.history.length < last.history.length) :
    ∃ notTerminal : ¬ middle.cut.Terminal,
      (last.history[middle.history.length]'shorter).event =
        assignedSelection assignment middle notTerminal := by
  rcases Relation.ReflTransGen.cases_head reach with same | ⟨next, step, rest⟩
  · subst same; omega
  obtain ⟨notTerminal, selected, chosen, member⟩ := step
  refine ⟨notTerminal, ?_⟩
  have selection : selected = selectAt middle.cut.enabled
      (enabled_nonempty_of_not_terminal middle notTerminal)
      (assignment (scheduleSite middle)) := by
    change selected ∈ ((PMF.pure (assignment (scheduleSite middle))).map _).support at chosen
    rw [PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at chosen
    exact chosen
  unfold eventStep at member
  rw [PMF.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨action, _, stepped⟩ := member
  obtain ⟨value, _, history⟩ := middle.step_completion _ _ action next stepped
  have kept := Config.Step.path_history_prefix (PlanReachable.toPath rest)
  have inside : middle.history.length < next.history.length := by
    rw [history]; simp
  rw [← kept.getElem inside]
  simp only [history, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem_cons_zero, EventGraph.completion]
  rw [selection]
  rfl

/-- A completed event keeps its output along a path. -/
theorem path_outputs_of_completed {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) {event : graph.EventId}
    (completed : event ∈ before.cut.completed) : after.outputs event = before.outputs event := by
  induction path with
  | refl => rfl
  | @tail middle last _ moved ih =>
      obtain ⟨stepped, ready, action, supported⟩ := moved
      rw [Config.step, PMF.support_map] at supported
      obtain ⟨value, _, rfl⟩ := supported
      have different : event ≠ stepped := by
        intro same
        subst same
        exact ready.1 (Config.Step.path_completed_mono (by assumption) completed)
      rw [middle.complete_output_of_ne stepped event ready action value different, ih]

omit [DecidableEq Player] in
private theorem mem_completed_iff (config : graph.Config) (event : graph.EventId) :
    event ∈ config.cut.completed ↔ event ∈ config.history.map EventCompletion.event :=
  (config.history_exact event).symm

omit [DecidableEq Player] in
/-- The default entry recorded with each completion of a history. -/
theorem history_map_defaultEvent (config : graph.Config) :
    config.history.map EventCompletion.defaultEvent =
      (config.history.map EventCompletion.event).map fun event =>
        (completionOf config event).bind EventCompletion.defaultEvent := by
  rw [List.map_map]
  refine List.map_congr_left fun completion member => ?_
  rw [Function.comp_apply,
    (completionOf_eq_some_iff config completion.event completion).mpr ⟨member, rfl⟩]
  rfl

/-- **Replay.** Two configurations reachable from initial configurations under
the same deterministic assigned scheduler, with the same completed events,
public store and default entries, list their completions in the same order. -/
theorem assigned_history_events_eq {profile : graph.BehavioralProfile}
    {assignment : graph.ScheduleSite → Option graph.EventId} {first second : graph.Inputs}
    {left right : graph.Config}
    (leftReach : PlanReachable profile (assignedScheduler assignment) (Config.initial first) left)
    (rightReach : PlanReachable profile (assignedScheduler assignment) (Config.initial second)
      right)
    (completed : left.cut.completed = right.cut.completed)
    (publicSame : graph.publicStore left.store = graph.publicStore right.store)
    (defaultsSame : ∀ event, (completionOf left event).bind EventCompletion.defaultEvent =
      (completionOf right event).bind EventCompletion.defaultEvent) :
    left.history.map EventCompletion.event = right.history.map EventCompletion.event := by
  have lengthOf (config : graph.Config) :
      config.history.length = config.cut.completed.card := by
    have exact : config.cut.completed = (config.history.map EventCompletion.event).toFinset := by
      ext event
      rw [List.mem_toFinset, ← mem_completed_iff]
    rw [exact, List.toFinset_card_of_nodup config.history_nodup, List.length_map]
  have lengths : left.history.length = right.history.length := by
    rw [lengthOf, lengthOf, completed]
  have recordsSame : (fun event => (completionOf left event).bind EventCompletion.defaultEvent) =
      fun event => (completionOf right event).bind EventCompletion.defaultEvent :=
    funext defaultsSame
  suffices prefixes : ∀ length ≤ left.history.length,
      (left.history.map EventCompletion.event).take length =
        (right.history.map EventCompletion.event).take length by
    have whole := prefixes left.history.length le_rfl
    rwa [List.take_of_length_le (by simp), List.take_of_length_le (by simp [lengths])] at whole
  intro length
  induction length with
  | zero => intro _; simp
  | succ length ih =>
      intro bound
      have earlier := ih (by omega)
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
      have cuts : middle.cut = other.cut := by
        ext event
        rw [mem_completed_iff, mem_completed_iff, events]
      have stores : graph.publicStore middle.store = graph.publicStore other.store := by
        funext field
        cases field with
        | inl input =>
            have middleInputs := Config.Step.path_inputs_eq (PlanReachable.toPath leftRest)
            have otherInputs := Config.Step.path_inputs_eq (PlanReachable.toPath rightRest)
            have same := congrFun publicSame (.inl input)
            simp only [publicStore, Config.store_input, ← middleInputs, ← otherInputs] at same ⊢
            exact same
        | inr event =>
            by_cases done : event ∈ middle.cut.completed
            · have otherDone : event ∈ other.cut.completed := cuts ▸ done
              have same := congrFun publicSame (.inr event)
              simp only [publicStore, Config.store_output,
                path_outputs_of_completed (PlanReachable.toPath leftRest) done,
                path_outputs_of_completed (PlanReachable.toPath rightRest) otherDone] at same ⊢
              exact same
            · have otherPending : event ∉ other.cut.completed := cuts ▸ done
              have middleNone : middle.outputs event = none :=
                Option.not_isSome_iff_eq_none.mp fun present =>
                  done ((middle.output_available event).mp present)
              have otherNone : other.outputs event = none :=
                Option.not_isSome_iff_eq_none.mp fun present =>
                  otherPending ((other.output_available event).mp present)
              simp only [publicStore, Config.store_output, middleNone, otherNone]
      have defaults : middle.defaults = other.defaults := by
        change EventCompletion.defaults middle.history = EventCompletion.defaults other.history
        simp only [EventCompletion.defaults]
        congr 2
        rw [middleHistory, otherHistory, List.map_take, List.map_take,
          history_map_defaultEvent left, history_map_defaultEvent right, recordsSame]
        have earlierMapped : (left.history.take length).map EventCompletion.event =
            (right.history.take length).map EventCompletion.event := by
          rw [List.map_take, List.map_take, earlier]
        simp only [← List.map_take]
        rw [earlierMapped]
      have sites : scheduleSite middle = scheduleSite other := by
        unfold scheduleSite
        rw [cuts]
        congr 1
        exact EventPublicObservation.ext events stores defaults
      obtain ⟨middleActive, leftEvent⟩ := leftRest.next_event (by omega)
      obtain ⟨otherActive, rightEvent⟩ := rightRest.next_event (by omega)
      have selections : assignedSelection assignment middle middleActive =
          assignedSelection assignment other otherActive := by
        unfold assignedSelection
        have selectCongr : ∀ (enabled enabled' : Finset graph.EventId) (same : enabled = enabled')
            (nonempty : enabled.Nonempty) (nonempty' : enabled'.Nonempty)
            (drawn drawn' : Option graph.EventId), drawn = drawn' →
            (selectAt enabled nonempty drawn).1 = (selectAt enabled' nonempty' drawn').1 := by
          intro enabled enabled' same nonempty nonempty' drawn drawn' sameDrawn
          subst same sameDrawn
          rfl
        exact selectCongr _ _ (by rw [cuts]) _ _ _ _ (by rw [sites])
      rw [List.take_add_one, List.take_add_one, earlier]
      congr 1
      simp only [List.getElem?_map]
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some]
      simp only [middleLength] at leftEvent
      simp only [otherLength] at rightEvent
      rw [leftEvent, rightEvent, selections]

omit [DecidableEq Player] in
/-- A public field is visible to every player. -/
theorem fieldVisibleTo_of_fieldPublic (who : Player) {field : graph.Field}
    (isPublic : graph.fieldPublic field) : graph.fieldVisibleTo who field := by
  unfold fieldPublic at isPublic
  unfold fieldVisibleTo
  cases kind : graph.layout field <;> simp_all [EventField.IsPublic, EventField.VisibleTo]

theorem publicStore_playerStore (who : Player) (store : EventGraph.Store graph.layout) :
    graph.publicStore (graph.playerStore who store) = graph.publicStore store := by
  funext field
  by_cases isPublic : graph.fieldPublic field
  · simp [publicStore, isPublic, playerStore, fieldVisibleTo_of_fieldPublic who isPublic]
  · simp [publicStore, isPublic]

omit [DecidableEq Player] in
private theorem filterMap_finRange_inj {β : Type} {count : Nat} (tag : β → Fin count)
    (left right : Fin count → Option β)
    (leftTagged : ∀ index item, left index = some item → tag item = index)
    (rightTagged : ∀ index item, right index = some item → tag item = index)
    (same : (List.finRange count).filterMap left = (List.finRange count).filterMap right) :
    left = right := by
  funext index
  have transfer (first second : Fin count → Option β)
      (firstTagged : ∀ index item, first index = some item → tag item = index)
      (secondTagged : ∀ index item, second index = some item → tag item = index)
      (lists : (List.finRange count).filterMap first = (List.finRange count).filterMap second)
      (item : β) (found : first index = some item) : second index = some item := by
    have member : item ∈ (List.finRange count).filterMap first :=
      List.mem_filterMap.mpr ⟨index, List.mem_finRange _, found⟩
    rw [lists] at member
    obtain ⟨other, _, otherFound⟩ := List.mem_filterMap.mp member
    have sameIndex : other = index :=
      (secondTagged other item otherFound).symm.trans (firstTagged index item found)
    rwa [sameIndex] at otherFound
  cases leftValue : left index with
  | some item => exact (transfer left right leftTagged rightTagged same item leftValue).symm
  | none =>
      cases rightValue : right index with
      | none => rfl
      | some item =>
          have := transfer right left rightTagged leftTagged same.symm item rightValue
          rw [leftValue] at this
          exact absurd this (by simp)

omit [DecidableEq Player] in
theorem mem_completed_iff_completionOf (config : graph.Config) (event : graph.EventId) :
    event ∈ config.cut.completed ↔ (completionOf config event).isSome := by
  rw [mem_completed_iff, completionOf, List.find?_isSome]
  simp [List.mem_map]

omit [DecidableEq Player] in
/-- A filtered history read through each event's completion record. -/
theorem history_filter_eq (config : graph.Config) (keep : graph.Completion → Bool) :
    config.history.filter keep =
      (config.history.map EventCompletion.event).filterMap fun event =>
        (completionOf config event).filter keep := by
  rw [List.filterMap_map]
  have each : ∀ completion ∈ config.history,
      (completionOf config completion.event).filter keep =
        if keep completion then some completion else none := by
    intro completion member
    rw [(completionOf_eq_some_iff config completion.event completion).mpr ⟨member, rfl⟩]
    cases kept : keep completion <;> simp [Option.filter, kept]
  symm
  calc _ = config.history.filterMap (fun completion =>
          if keep completion then some completion else none) :=
        List.filterMap_congr fun completion member => each completion member
    _ = _ := by
      induction config.history with
      | nil => rfl
      | cons head tail ih => cases kept : keep head <;> simp [kept, ih]

/-- **Replayed observations.** Under one deterministic assigned scheduler, two
reachable configurations that give a player the same normalized observation
give it the same actual observation. -/
theorem assigned_playerObserve_eq {profile : graph.BehavioralProfile}
    {assignment : graph.ScheduleSite → Option graph.EventId} {first second : graph.Inputs}
    {left right : graph.Config}
    (leftReach : PlanReachable profile (assignedScheduler assignment) (Config.initial first) left)
    (rightReach : PlanReachable profile (assignedScheduler assignment) (Config.initial second)
      right) (who : Player)
    (same : graph.normalizeObservation who (graph.playerObserve who left) =
      graph.normalizeObservation who (graph.playerObserve who right)) :
    graph.playerObserve who left = graph.playerObserve who right := by
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at same
  have orders := congrArg EventPlayerObservation.completionOrder same
  have stores := congrArg EventPlayerObservation.store same
  have owns := congrArg EventPlayerObservation.ownActions same
  have defaults := congrArg (fun observation => observation.defaults.events) same
  simp only [List.reverse_inj] at orders stores owns defaults
  have completed : left.cut.completed = right.cut.completed := by
    ext event
    rw [mem_completed_iff_completionOf, mem_completed_iff_completionOf]
    have member := congrArg (fun events => event ∈ events) orders
    simpa [List.mem_filter] using member
  have publicSame : graph.publicStore left.store = graph.publicStore right.store := by
    rw [← publicStore_playerStore who left.store, ← publicStore_playerStore who right.store]
    exact congrArg graph.publicStore stores
  have defaultsSame : ∀ event, (completionOf left event).bind EventCompletion.defaultEvent =
      (completionOf right event).bind EventCompletion.defaultEvent := by
    intro event
    by_cases done : (completionOf left event).isSome
    · have inList : event ∈ (List.finRange graph.order.eventCount).filter fun event =>
          (completionOf left event).isSome := by simp [done]
      rw [orders] at defaults
      exact List.map_inj_left.mp defaults event (orders ▸ inList)
    · have rightDone : ¬ (completionOf right event).isSome := by
        rwa [← mem_completed_iff_completionOf, ← completed, mem_completed_iff_completionOf]
      rw [Option.not_isSome_iff_eq_none.mp done, Option.not_isSome_iff_eq_none.mp rightDone]
  have events := assigned_history_events_eq leftReach rightReach completed publicSame
    defaultsSame
  have ownSame := filterMap_finRange_inj EventCompletion.event _ _
    (fun event completion found => by
      obtain ⟨found, _⟩ := Option.filter_eq_some_iff.mp found
      exact ((completionOf_eq_some_iff left event completion).mp found).2)
    (fun event completion found => by
      obtain ⟨found, _⟩ := Option.filter_eq_some_iff.mp found
      exact ((completionOf_eq_some_iff right event completion).mp found).2) owns
  apply EventPlayerObservation.ext
  · exact events
  · exact stores
  · change graph.ownCompletions who left.history = graph.ownCompletions who right.history
    unfold ownCompletions
    rw [history_filter_eq, history_filter_eq, events]
    exact congrArg (fun read => (right.history.map EventCompletion.event).filterMap read) ownSame
  · change EventCompletion.defaults left.history = EventCompletion.defaults right.history
    simp only [EventCompletion.defaults]
    rw [history_map_defaultEvent left, history_map_defaultEvent right, events]
    congr 2
    exact List.map_congr_left fun event _ => defaultsSame event

/-- Profiles with the same action laws at every ready event of every reachable
configuration give the same run. -/
theorem runPlan_congr_profile (left right : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) :
    ∀ fuel (config : graph.Config),
      (∀ next, PlanReachable left scheduler config next → ∀ event, next.cut.Ready event →
        actionLaw left next event = actionLaw right next event) →
      graph.runPlan (graph.policyPlan left scheduler) fuel config =
        graph.runPlan (graph.policyPlan right scheduler) fuel config := by
  intro fuel
  induction fuel with
  | zero => intro config _; rfl
  | succ fuel ih =>
      intro config agree
      by_cases terminal : config.cut.Terminal
      · simp only [EventGraph.runPlan, dite_eq_left terminal]
      · rw [runPlan_policyPlan_succ left scheduler fuel config terminal,
          runPlan_policyPlan_succ right scheduler fuel config terminal]
        apply bind_congr_on_support _
        intro selected chosen
        have ready := (EventOrder.Cut.mem_enabled _ _).mp selected.2
        unfold eventStep
        rw [← agree config Relation.ReflTransGen.refl selected.1 ready]
        apply bind_congr_on_support _
        intro next member
        apply ih next
        intro later reach
        exact agree later (Relation.ReflTransGen.head ⟨terminal, selected, chosen,
          by unfold eventStep; exact member⟩ reach)

private theorem policy_congr' {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : graph.actor? event = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

/-- A policy that reads only its normalized observation: it plays the original
policy at the actual observation of a configuration reachable under the given
deterministic scheduler with that normalized observation. -/
def replayPolicy (profile : graph.BehavioralProfile)
    (assignment : graph.ScheduleSite → Option graph.EventId) (who : Player)
    (policy : graph.BehavioralPolicy who) : graph.BehavioralPolicy who :=
  fun event actor observation active =>
    open Classical in
    if found : ∃ (inputs : graph.Inputs) (config : graph.Config),
        PlanReachable profile (assignedScheduler assignment) (Config.initial inputs) config ∧
          graph.normalizeObservation who (graph.playerObserve who config) = observation ∧
          who ∉ (graph.playerObserve who config).defaulted then
      policy event actor (graph.playerObserve who found.choose_spec.choose)
        found.choose_spec.choose_spec.2.2
    else policy event actor observation active

/-- **Replay law.** Under a deterministic assigned scheduler, replacing one
player's policy by the normalization of its replay leaves every run unchanged. -/
theorem runPolicies_replay (profile : graph.BehavioralProfile)
    (assignment : graph.ScheduleSite → Option graph.EventId) (who : Player)
    (inputs : graph.Inputs) :
    graph.runPolicies (assignedScheduler assignment)
        (GameTheory.Profile.update (sig := graph.gameSignature) profile who
          (graph.normalizePolicy who (replayPolicy profile assignment who (profile who))))
        inputs =
      graph.runPolicies (assignedScheduler assignment) profile inputs := by
  unfold EventGraph.runPolicies EventGraph.run
  symm
  apply runPlan_congr_profile
  intro config reach event _
  cases ownerEq : (graph.nodes event).actor with
  | none => rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
  | some owner =>
      rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
      by_cases inactive : owner ∈ config.defaulted
      · rw [dite_eq_left inactive, dite_eq_left inactive]
      rw [dite_eq_right inactive, dite_eq_right inactive]
      by_cases same : owner = who
      · subst owner
        rw [GameTheory.Profile.update_same]
        change _ = replayPolicy profile assignment who (profile who) event ownerEq _ _
        unfold replayPolicy
        have found : ∃ (initial : graph.Inputs) (other : graph.Config),
            PlanReachable profile (assignedScheduler assignment) (Config.initial initial) other ∧
              graph.normalizeObservation who (graph.playerObserve who other) =
                graph.normalizeObservation who (graph.playerObserve who config) ∧
              who ∉ (graph.playerObserve who other).defaulted :=
          ⟨inputs, config, reach, rfl, inactive⟩
        rw [dite_eq_left found]
        exact policy_congr' (profile who) event ownerEq
          (assigned_playerObserve_eq reach found.choose_spec.choose_spec.1 who
            found.choose_spec.choose_spec.2.1.symm) _ _
      · rw [GameTheory.Profile.update_of_ne _ _ same]

end Vegas.EventGraph
