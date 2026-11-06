/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.NormalizedPolicy

/-! # Restricting normalized observations

A configuration is the restriction of another to a set of events when it
records exactly the completions of those events and stores exactly their
outputs and the inputs. A player's normalized observation of a restriction is
read from its normalized observation of the larger configuration: equal
normalized observations of two larger configurations give equal normalized
observations of their restrictions to one set.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A field lies in a set of events when it is an input or an output of one. -/
def FieldWithin (events : graph.EventId → Prop) : graph.Field → Prop
  | .inl _ => True
  | .inr event => events event

instance (events : graph.EventId → Prop) [DecidablePred events] :
    DecidablePred (FieldWithin (graph := graph) events) := fun field =>
  match field with
  | .inl _ => isTrue trivial
  | .inr event => inferInstanceAs (Decidable (events event))

/-- **Restriction.** `small` records exactly the completions of `large` at the
events of a set, and stores exactly the fields of `large` within it. -/
structure Config.RestrictionOf (events : graph.EventId → Prop) [DecidablePred events]
    (small large : graph.Config) : Prop where
  records : ∀ event, completionOf small event =
    if events event then completionOf large event else none
  store : ∀ field, small.store field =
    if FieldWithin events field then large.store field else none

omit [DecidableEq Player] in
/-- A list of records tagged by their events, taken over the ranks, returns each
event's record. -/
theorem find?_filterMap_tagged (records : graph.EventId → Option graph.Completion)
    (tagged : ∀ event completion, records event = some completion → completion.event = event)
    (event : graph.EventId) :
    ((List.finRange graph.order.eventCount).filterMap records).find?
        (fun completion => completion.event = event) = records event := by
  rw [List.find?_filterMap]
  cases recorded : records event with
  | none =>
      have absent : (List.finRange graph.order.eventCount).find?
          (fun other => (records other).any fun completion => completion.event = event) = none := by
        apply List.find?_eq_none.mpr
        intro other _ hit
        cases other_records : records other with
        | none => simp [other_records] at hit
        | some completion =>
            have same : completion.event = event := by simpa [other_records] using hit
            have tag := tagged other completion other_records
            rw [tag] at same
            rw [same, recorded] at other_records
            cases other_records
      rw [absent]
      rfl
  | some completion =>
      have tag := tagged event completion recorded
      have found : (List.finRange graph.order.eventCount).find?
          (fun other => (records other).any fun completion => completion.event = event) =
            some event := by
        apply List.find?_eq_some_iff_getElem.mpr
        refine ⟨by simp [recorded, tag], ?_⟩
        refine ⟨event.val, by simp, by simp, ?_⟩
        intro index smaller
        have bound : index < graph.order.eventCount := by
          have := event.isLt
          omega
        have positioned : (List.finRange graph.order.eventCount)[index]'(by simp [bound]) =
            ⟨index, bound⟩ := by
          simp
        rw [positioned]
        cases other_records : records ⟨index, bound⟩ with
        | none => simp
        | some other =>
            have otherTag := tagged _ other other_records
            have different : other.event ≠ event := by
              rw [otherTag]
              intro same
              have := congrArg Fin.val same
              simp only at this
              omega
            simp [different]
      rw [found]
      simp [recorded]

omit [DecidableEq Player] in
theorem completionOf_tagged (config : graph.Config) (event : graph.EventId)
    (completion : graph.Completion) (found : completionOf config event = some completion) :
    completion.event = event := by
  unfold completionOf at found
  simpa using List.find?_some found

omit [DecidableEq Player] in
theorem completionOf_filter_tagged (config : graph.Config) (keep : graph.Completion → Bool)
    (event : graph.EventId) (completion : graph.Completion)
    (found : (completionOf config event).filter keep = some completion) :
    completion.event = event := by
  cases recorded : completionOf config event with
  | none => simp [recorded] at found
  | some record =>
      rw [recorded, Option.filter] at found
      split at found
      · cases found
        exact completionOf_tagged config event _ recorded
      · cases found

/-- **Restrictions of indistinguishable configurations are indistinguishable.** -/
theorem normalizeObservation_playerObserve_restrict (who : Player)
    (events : graph.EventId → Prop) [DecidablePred events]
    {small large small' large' : graph.Config}
    (restricted : small.RestrictionOf events large)
    (restricted' : small'.RestrictionOf events large')
    (same : graph.normalizeObservation who (graph.playerObserve who large) =
      graph.normalizeObservation who (graph.playerObserve who large')) :
    graph.normalizeObservation who (graph.playerObserve who small) =
      graph.normalizeObservation who (graph.playerObserve who small') := by
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at same ⊢
  have orders : ((List.finRange graph.order.eventCount).filter fun event =>
      (completionOf large event).isSome) =
      (List.finRange graph.order.eventCount).filter fun event =>
        (completionOf large' event).isSome :=
    congrArg EventPlayerObservation.completionOrder same
  have stores : graph.playerStore who large.store = graph.playerStore who large'.store :=
    congrArg EventPlayerObservation.store same
  have owns : ((List.finRange graph.order.eventCount).filterMap fun event =>
      (completionOf large event).filter fun completion =>
        graph.actor? completion.event = some who ∧ completion.decision.isSome) =
      (List.finRange graph.order.eventCount).filterMap fun event =>
        (completionOf large' event).filter fun completion =>
          graph.actor? completion.event = some who ∧ completion.decision.isSome :=
    congrArg EventPlayerObservation.ownActions same
  have histories : (((List.finRange graph.order.eventCount).filter fun event =>
      (completionOf large event).isSome).map fun event =>
        (completionOf large event).bind EventCompletion.defaultEvent).reverse =
      (((List.finRange graph.order.eventCount).filter fun event =>
        (completionOf large' event).isSome).map fun event =>
          (completionOf large' event).bind EventCompletion.defaultEvent).reverse :=
    congrArg (fun view => view.defaults.events) same
  have present (event : graph.EventId) :
      (completionOf large event).isSome = (completionOf large' event).isSome := by
    have member := congrArg (fun list => event ∈ list) orders
    simp only [List.mem_filter, List.mem_finRange, true_and, eq_iff_iff] at member
    exact Bool.eq_iff_iff.mpr member
  have own (event : graph.EventId) :
      (completionOf large event).filter (fun completion =>
          graph.actor? completion.event = some who ∧ completion.decision.isSome) =
        (completionOf large' event).filter (fun completion =>
          graph.actor? completion.event = some who ∧ completion.decision.isSome) := by
    have found := congrArg (fun list => list.find? fun completion => completion.event = event) owns
    rw [find?_filterMap_tagged _ (completionOf_filter_tagged large _) event,
      find?_filterMap_tagged _ (completionOf_filter_tagged large' _) event] at found
    exact found
  have sameFilter : ((List.finRange graph.order.eventCount).filter fun event =>
      (completionOf large event).isSome) =
      (List.finRange graph.order.eventCount).filter fun event =>
        (completionOf large' event).isSome :=
    List.filter_congr fun event _ => present event
  have defaultsEach : ∀ event, (completionOf large event).isSome →
      (completionOf large event).bind EventCompletion.defaultEvent =
        (completionOf large' event).bind EventCompletion.defaultEvent := by
    intro event isPresent
    rw [sameFilter, List.reverse_inj] at histories
    exact (List.map_inj_left.mp histories) event
      (by rw [List.mem_filter]; exact ⟨List.mem_finRange _, by rw [← present]; exact isPresent⟩)
  have smallPresent (event : graph.EventId) :
      (completionOf small event).isSome = (completionOf small' event).isSome := by
    rw [restricted.records, restricted'.records]
    split
    · exact present event
    · rfl
  have smallFilter : ((List.finRange graph.order.eventCount).filter fun event =>
      (completionOf small event).isSome) =
      (List.finRange graph.order.eventCount).filter fun event =>
        (completionOf small' event).isSome :=
    List.filter_congr fun event _ => smallPresent event
  apply EventPlayerObservation.ext
  · exact smallFilter
  · change graph.playerStore who small.store = graph.playerStore who small'.store
    funext field
    have visible := congrFun stores field
    unfold playerStore at visible ⊢
    rw [restricted.store, restricted'.store]
    by_cases shown : graph.fieldVisibleTo who field
    · rw [ite_eq_left shown, ite_eq_left shown] at visible ⊢
      by_cases within : FieldWithin events field
      · rw [ite_eq_left within, ite_eq_left within]
        exact visible
      · rw [ite_eq_right within, ite_eq_right within]
    · rw [ite_eq_right shown, ite_eq_right shown]
  · change List.filterMap _ _ = List.filterMap _ _
    congr 1
    funext event
    rw [restricted.records, restricted'.records]
    split
    · exact own event
    · rfl
  · change DefaultHistory.mk _ = DefaultHistory.mk _
    rw [smallFilter]
    congr 2
    apply List.map_congr_left
    intro event member
    rw [List.mem_filter] at member
    have isPresent := member.2
    rw [← smallPresent] at isPresent
    rw [restricted.records] at isPresent
    rw [restricted.records, restricted'.records]
    split at isPresent
    · rw [ite_eq_left (by assumption), ite_eq_left (by assumption)]
      exact defaultsEach event isPresent
    · simp at isPresent

end Vegas.EventGraph
