/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.NormalizedRestriction
import Vegas.EventGraph.SchedulerErasure
import Vegas.EventGraph.CanonicalStep

/-! # Prefix configurations are restrictions of their successors

A configuration whose cut is a rank prefix is the restriction to that prefix of
every configuration a path of graph steps reaches from it: steps keep inputs,
stored outputs and completion records. Hence the normalized observation of a
prefix configuration is read from the normalized observation of any successor.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- An event has a completion record exactly when it is completed. -/
theorem completionOf_isSome_iff (config : graph.Config) (event : graph.EventId) :
    (completionOf config event).isSome ↔ event ∈ config.cut.completed := by
  unfold completionOf
  rw [List.find?_isSome, ← config.history_exact]
  simp [List.mem_map]

omit [DecidableEq Player] in
theorem completionOf_eq_none_iff (config : graph.Config) (event : graph.EventId) :
    completionOf config event = none ↔ event ∉ config.cut.completed := by
  rw [← completionOf_isSome_iff, Option.not_isSome_iff_eq_none]

/-- Stored values persist along graph paths. -/
theorem Config.Step.path_store_of_some {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) (field : graph.Field)
    (value : (graph.layout field).Value) (stored : before.store field = some value) :
    after.store field = some value := by
  induction path with
  | refl => exact stored
  | tail _ moved previous =>
      obtain ⟨event, ready, action, member⟩ := moved
      exact Config.step_store_of_some _ _ event ready action member field value previous

/-- Completion records persist along graph paths. -/
theorem Config.Step.path_completionOf_of_some {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) (event : graph.EventId)
    (completion : graph.Completion) (found : completionOf before event = some completion) :
    completionOf after event = some completion := by
  obtain ⟨member, same⟩ := (completionOf_eq_some_iff before event completion).mp found
  obtain ⟨extra, extended⟩ := Config.Step.path_history_prefix path
  apply (completionOf_eq_some_iff after event completion).mpr
  refine ⟨?_, same⟩
  rw [← extended]
  exact List.mem_append_left _ member

/-- **A prefix configuration is the restriction of its successors.** -/
theorem Config.restrictionOf_path {before after : graph.Config} {rank : Nat}
    (ordered : before.cut.IsPrefix rank)
    (path : Relation.ReflTransGen Config.Step before after) :
    before.RestrictionOf (fun event => event.val < rank) after where
  records event := by
    by_cases smaller : event.val < rank
    · rw [ite_eq_left smaller]
      have completed : event ∈ before.cut.completed := (ordered.2 event).mpr smaller
      obtain ⟨completion, found⟩ :=
        Option.isSome_iff_exists.mp ((completionOf_isSome_iff before event).mpr completed)
      rw [found, Config.Step.path_completionOf_of_some path event completion found]
    · rw [ite_eq_right smaller]
      exact (completionOf_eq_none_iff before event).mpr fun completed =>
        smaller ((ordered.2 event).mp completed)
  store field := by
    cases field with
    | inl input =>
        rw [ite_eq_left (show FieldWithin (fun event : graph.EventId => event.val < rank)
          (.inl input) from trivial)]
        change some (before.inputs input) = some (after.inputs input)
        rw [Config.Step.path_inputs_eq path]
    | inr event =>
        by_cases smaller : event.val < rank
        · rw [ite_eq_left (show FieldWithin (fun event : graph.EventId => event.val < rank)
            (.inr event) from smaller)]
          have completed : event ∈ before.cut.completed := (ordered.2 event).mpr smaller
          obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
            ((before.output_available event).mpr completed)
          change before.outputs event = after.store (.inr event)
          rw [stored]
          exact (Config.Step.path_store_of_some path (.inr event) value stored).symm
        · rw [ite_eq_right (show ¬ FieldWithin (fun event : graph.EventId => event.val < rank)
            (.inr event) from smaller)]
          change before.outputs event = none
          exact Option.not_isSome_iff_eq_none.mp fun available =>
            smaller ((ordered.2 event).mp ((before.output_available event).mp available))

/-- **Prefix views are read from successor views.** -/
theorem normalizeObservation_playerObserve_of_paths (who : Player) {rank : Nat}
    {before after before' after' : graph.Config}
    (ordered : before.cut.IsPrefix rank) (ordered' : before'.cut.IsPrefix rank)
    (path : Relation.ReflTransGen Config.Step before after)
    (path' : Relation.ReflTransGen Config.Step before' after')
    (same : graph.normalizeObservation who (graph.playerObserve who after) =
      graph.normalizeObservation who (graph.playerObserve who after')) :
    graph.normalizeObservation who (graph.playerObserve who before) =
      graph.normalizeObservation who (graph.playerObserve who before') :=
  normalizeObservation_playerObserve_restrict who _ (Config.restrictionOf_path ordered path)
    (Config.restrictionOf_path ordered' path') same

/-- A restriction to completed events stays a restriction along graph paths. -/
theorem Config.RestrictionOf.trans_path {events : graph.EventId → Prop} [DecidablePred events]
    {small middle large : graph.Config} (restricted : small.RestrictionOf events middle)
    (within : ∀ event, events event → event ∈ middle.cut.completed)
    (path : Relation.ReflTransGen Config.Step middle large) :
    small.RestrictionOf events large where
  records event := by
    rw [restricted.records]
    by_cases inside : events event
    · rw [ite_eq_left inside, ite_eq_left inside]
      obtain ⟨completion, found⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff middle event).mpr (within event inside))
      rw [found, Config.Step.path_completionOf_of_some path event completion found]
    · rw [ite_eq_right inside, ite_eq_right inside]
  store field := by
    rw [restricted.store]
    by_cases inside : FieldWithin events field
    · rw [ite_eq_left inside, ite_eq_left inside]
      have available : (middle.store field).isSome := by
        cases field with
        | inl input => rfl
        | inr event =>
            change (middle.outputs event).isSome = true
            exact (middle.output_available event).mpr (within event inside)
      obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp available
      rw [stored, Config.Step.path_store_of_some path field value stored]
    · rw [ite_eq_right inside, ite_eq_right inside]

/-- A prefix configuration is the restriction of its completion at a later event. -/
theorem Config.restrictionOf_complete {config : graph.Config} {rank : Nat}
    (ordered : config.cut.IsPrefix rank) (event : graph.EventId) (ready : config.cut.Ready event)
    (late : rank ≤ event.val) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    config.RestrictionOf (fun other => other.val < rank)
      (config.complete event ready action value) where
  records other := by
    by_cases smaller : other.val < rank
    · rw [ite_eq_left smaller, completionOf_complete, Function.update_of_ne]
      intro same
      subst same
      omega
    · rw [ite_eq_right smaller]
      exact (completionOf_eq_none_iff config other).mpr fun completed =>
        smaller ((ordered.2 other).mp completed)
  store field := by
    cases field with
    | inl input =>
        rw [ite_eq_left (show FieldWithin (fun other : graph.EventId => other.val < rank)
          (.inl input) from trivial)]
        rfl
    | inr other =>
        by_cases smaller : other.val < rank
        · rw [ite_eq_left (show FieldWithin (fun other : graph.EventId => other.val < rank)
            (.inr other) from smaller)]
          change config.outputs other = (config.complete event ready action value).outputs other
          rw [config.complete_output_of_ne event other ready action value]
          intro same
          subst same
          omega
        · rw [ite_eq_right (show ¬ FieldWithin (fun other : graph.EventId => other.val < rank)
            (.inr other) from smaller)]
          change config.outputs other = none
          exact Option.not_isSome_iff_eq_none.mp fun available =>
            smaller ((ordered.2 other).mp ((config.output_available other).mp available))

/-- **Prefix views are read from views after completing a later event and
taking graph steps.** -/
theorem normalizeObservation_playerObserve_of_complete_paths (who : Player) {rank : Nat}
    {before after before' after' : graph.Config}
    (ordered : before.cut.IsPrefix rank) (ordered' : before'.cut.IsPrefix rank)
    (event : graph.EventId) (ready : before.cut.Ready event) (ready' : before'.cut.Ready event)
    (late : rank ≤ event.val) (action action' : graph.Action event)
    (value value' : (graph.outputLayout event).Value)
    (path : Relation.ReflTransGen Config.Step (before.complete event ready action value) after)
    (path' : Relation.ReflTransGen Config.Step (before'.complete event ready' action' value')
      after')
    (same : graph.normalizeObservation who (graph.playerObserve who after) =
      graph.normalizeObservation who (graph.playerObserve who after')) :
    graph.normalizeObservation who (graph.playerObserve who before) =
      graph.normalizeObservation who (graph.playerObserve who before') := by
  have within (config : graph.Config) (configOrdered : config.cut.IsPrefix rank)
      (configReady : config.cut.Ready event) (chosen : graph.Action event)
      (output : (graph.outputLayout event).Value) :
      ∀ other : graph.EventId, other.val < rank →
        other ∈ (config.complete event configReady chosen output).cut.completed := by
    intro other smaller
    rw [Config.complete_cut, EventOrder.Cut.mem_complete]
    exact Or.inr ((configOrdered.2 other).mpr smaller)
  exact normalizeObservation_playerObserve_restrict who _
    ((Config.restrictionOf_complete ordered event ready late action value).trans_path
      (within before ordered ready action value) path)
    ((Config.restrictionOf_complete ordered' event ready' late action' value').trans_path
      (within before' ordered' ready' action' value') path') same

end Vegas.EventGraph
