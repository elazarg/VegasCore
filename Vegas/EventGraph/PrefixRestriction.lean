module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.NormalizedRestriction
public import Vegas.EventGraph.SchedulerErasure
public import Vegas.EventGraph.CanonicalStep
public import Vegas.EventGraph.ResolutionProvenance

@[expose] public section

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

/-- Equal normalized observations have the same completed events. -/
theorem normalize_present_congr (who : Player) {left right : graph.Config}
    (same : graph.normalizeObservation who (graph.playerObserve who left) =
      graph.normalizeObservation who (graph.playerObserve who right)) (event : graph.EventId) :
    (completionOf left event).isSome = (completionOf right event).isSome := by
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at same
  have orders : ((List.finRange graph.order.eventCount).filter fun event =>
      (completionOf left event).isSome) =
      (List.finRange graph.order.eventCount).filter fun event =>
        (completionOf right event).isSome :=
    congrArg EventPlayerObservation.completionOrder same
  have member := congrArg (fun list => event ∈ list) orders
  simp only [List.mem_filter, List.mem_finRange, true_and, eq_iff_iff] at member
  exact Bool.eq_iff_iff.mpr member

/-- Equal normalized observations record the same default entry at every
completed event. -/
theorem normalize_defaultEvent_congr (who : Player) {left right : graph.Config}
    (same : graph.normalizeObservation who (graph.playerObserve who left) =
      graph.normalizeObservation who (graph.playerObserve who right)) (event : graph.EventId)
    (present : (completionOf left event).isSome) :
    (completionOf left event).bind EventCompletion.defaultEvent =
      (completionOf right event).bind EventCompletion.defaultEvent := by
  have presentEach := normalize_present_congr who same
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at same
  have histories : (((List.finRange graph.order.eventCount).filter fun event =>
      (completionOf left event).isSome).map fun event =>
        (completionOf left event).bind EventCompletion.defaultEvent).reverse =
      (((List.finRange graph.order.eventCount).filter fun event =>
        (completionOf right event).isSome).map fun event =>
          (completionOf right event).bind EventCompletion.defaultEvent).reverse :=
    congrArg (fun view => view.defaults.events) same
  have sameFilter : ((List.finRange graph.order.eventCount).filter fun event =>
      (completionOf left event).isSome) =
      (List.finRange graph.order.eventCount).filter fun event =>
        (completionOf right event).isSome :=
    List.filter_congr fun event _ => presentEach event
  rw [sameFilter, List.reverse_inj] at histories
  exact (List.map_inj_left.mp histories) event
    (by rw [List.mem_filter]; exact ⟨List.mem_finRange _, by rw [← presentEach]; exact present⟩)

/-- Equal normalized observations have the same defaulted players. -/
theorem normalize_defaulted_congr (who : Player) {left right : graph.Config}
    (same : graph.normalizeObservation who (graph.playerObserve who left) =
      graph.normalizeObservation who (graph.playerObserve who right)) :
    left.defaulted = right.defaulted := by
  ext player
  rw [mem_defaulted_iff_completionOf, mem_defaulted_iff_completionOf]
  constructor
  · rintro ⟨event, found⟩
    have present : (completionOf left event).isSome := by
      cases recorded : completionOf left event with
      | none => rw [recorded] at found; cases found
      | some _ => rfl
    exact ⟨event, (normalize_defaultEvent_congr who same event present).symm.trans found⟩
  · rintro ⟨event, found⟩
    have present : (completionOf right event).isSome := by
      cases recorded : completionOf right event with
      | none => rw [recorded] at found; cases found
      | some _ => rfl
    exact ⟨event, (normalize_defaultEvent_congr who same.symm event present).symm.trans found⟩


/-- A newly completed event has an actual ready transition along the path. -/
theorem Config.Step.path_at_completion
    {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) (event : graph.EventId)
    (pending : event ∉ before.cut.completed) (completed : event ∈ after.cut.completed) :
    ∃ (current next : graph.Config) (ready : current.cut.Ready event)
      (action : graph.Action event) (value : (graph.outputLayout event).Value),
      Relation.ReflTransGen Config.Step before current ∧
      next ∈ (current.step event ready action).support ∧
      Relation.ReflTransGen Config.Step next after ∧
      completionOf after event = some
        (EventGraph.completion graph event (current.actualDecision event action) value) ∧
      after.outputs event = some value := by
  revert pending
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => intro pending; exact (pending completed).elim
  | @head before middle moved rest ih =>
      intro pending
      obtain ⟨other, ready, action, supported⟩ := moved
      by_cases same : other = event
      · subst other
        have actual := supported
        rw [Config.step, PMF.mem_support_map_iff] at supported
        obtain ⟨value, _chosen, rfl⟩ := supported
        refine ⟨before, _, ready, action, value, .refl, actual, rest, ?_, ?_⟩
        · apply Config.Step.path_completionOf_of_some rest event _
          rw [completionOf_complete, Function.update_self]
        · exact Config.Step.path_store_of_some rest (.inr event) value
            (before.complete_output_same event ready action value)
      · have middlePending : event ∉ middle.cut.completed := by
          rw [before.step_cut other ready action middle supported,
            EventOrder.Cut.mem_complete]
          intro member
          rcases member with equal | old
          · exact same equal.symm
          · exact pending old
        obtain ⟨current, next, ready', action', value, prefixPath, chosen, suffixPath, record,
          output⟩ := ih middlePending
        refine ⟨current, next, ready', action', value,
          (Relation.ReflTransGen.single ⟨other, ready, action, supported⟩).trans prefixPath,
          chosen, suffixPath, record, output⟩


open GameTheory.Math.Probability

/-- **A configuration is the restriction of its successors to its completed
events.** -/
theorem Config.restrictionOf_completed_path {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) :
    before.RestrictionOf (fun event => event ∈ before.cut.completed) after where
  records event := by
    by_cases done : event ∈ before.cut.completed
    · rw [ite_eq_left done]
      obtain ⟨completion, found⟩ :=
        Option.isSome_iff_exists.mp ((completionOf_isSome_iff before event).mpr done)
      rw [found, Config.Step.path_completionOf_of_some path event completion found]
    · rw [ite_eq_right done]
      exact (completionOf_eq_none_iff before event).mpr done
  store field := by
    cases field with
    | inl input =>
        rw [ite_eq_left (show FieldWithin (fun event : graph.EventId =>
          event ∈ before.cut.completed) (.inl input) from trivial)]
        change some (before.inputs input) = some (after.inputs input)
        rw [Config.Step.path_inputs_eq path]
    | inr event =>
        by_cases done : event ∈ before.cut.completed
        · rw [ite_eq_left (show FieldWithin (fun event : graph.EventId =>
            event ∈ before.cut.completed) (.inr event) from done)]
          obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
            ((before.output_available event).mpr done)
          change before.outputs event = after.store (.inr event)
          rw [stored]
          exact (Config.Step.path_store_of_some path (.inr event) value stored).symm
        · rw [ite_eq_right (show ¬ FieldWithin (fun event : graph.EventId =>
            event ∈ before.cut.completed) (.inr event) from done)]
          change before.outputs event = none
          exact Option.not_isSome_iff_eq_none.mp fun available =>
            done ((before.output_available event).mp available)

/-- Equal full-key continuation laws retain identical past records and stores.
Only containment of the completed cuts is needed; the two policies may differ. -/
theorem Config.restrictionOf_of_canonicalLaw_eq
    (leftProfile rightProfile : graph.BehavioralProfile) (small large : graph.Config)
    (within : small.cut.completed ⊆ large.cut.completed)
    (same : canonicalLaw leftProfile small = canonicalLaw rightProfile large) :
    small.RestrictionOf (fun event => event ∈ small.cut.completed) large := by
  obtain ⟨key, member⟩ := (canonicalLaw leftProfile small).support_nonempty
  obtain ⟨left, leftMember, leftKey⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have other : key ∈ (canonicalLaw rightProfile large).support := by rwa [← same]
  obtain ⟨right, rightMember, rightKey⟩ := (PMF.mem_support_map_iff _ _ _).mp other
  have keys : runKey left = runKey right := leftKey.trans rightKey.symm
  have leftRestricted := Config.restrictionOf_completed_path
    (runPlan_graph_steps (graph.policyPlan leftProfile graph.canonicalScheduler)
      small.remaining small left leftMember)
  have rightRestricted := Config.restrictionOf_completed_path
    (runPlan_graph_steps (graph.policyPlan rightProfile graph.canonicalScheduler)
      large.remaining large right rightMember)
  refine ⟨fun event => ?_, fun field => ?_⟩
  · by_cases done : event ∈ small.cut.completed
    · simp only [leftRestricted.records, rightRestricted.records, ite_eq_left done,
        ite_eq_left (within done)]
      exact congrArg (fun image => image.2.2 event) keys
    · simp only [leftRestricted.records, ite_eq_right done]
  · cases field with
    | inl input =>
      simp only [leftRestricted.store, rightRestricted.store, FieldWithin, ite_true]
      exact congrArg (fun image => image.2.1 (.inl input)) keys
    | inr event =>
      by_cases done : event ∈ small.cut.completed
      · simp only [leftRestricted.store, rightRestricted.store, FieldWithin,
          ite_eq_left done, ite_eq_left (within done)]
        exact congrArg (fun image => image.2.1 (.inr event)) keys
      · simp only [leftRestricted.store, FieldWithin, ite_eq_right done]

/-- At the same cut, equal full-key continuation laws determine the current key. -/
theorem Config.runKey_eq_of_canonicalLaw_eq
    (leftProfile rightProfile : graph.BehavioralProfile) (left right : graph.Config)
    (cuts : left.cut = right.cut)
    (same : canonicalLaw leftProfile left = canonicalLaw rightProfile right) :
    runKey left = runKey right := by
  have restricted := Config.restrictionOf_of_canonicalLaw_eq leftProfile rightProfile left right
    (by rw [cuts]) same
  refine Prod.ext cuts (Prod.ext ?_ ?_)
  · funext field
    change left.store field = right.store field
    rw [restricted.store]
    cases field with
    | inl input => rfl
    | inr event =>
      change (if event ∈ left.cut.completed then right.store (.inr event) else none) = _
      by_cases done : event ∈ left.cut.completed
      · rw [ite_eq_left done]
      · rw [ite_eq_right done]
        exact (Option.not_isSome_iff_eq_none.mp fun available =>
          done (by rw [cuts]; exact (right.output_available event).mp available)).symm
  · funext event
    change completionOf left event = completionOf right event
    rw [restricted.records]
    by_cases done : event ∈ left.cut.completed
    · rw [ite_eq_left done]
    · rw [ite_eq_right done]
      exact (completionOf_eq_none_iff right event).mpr (by rwa [← cuts]) |>.symm

/-- A ready publication sees the successful binding and guard verdict recorded
by a donor with the same full canonical continuation law. -/
theorem Config.Reachable.ready_publication_of_canonicalLaw_eq
    {inputs : graph.Inputs} {current : graph.Config} (reachable : current.Reachable inputs)
    (currentProfile donorProfile : graph.BehavioralProfile) (donor : graph.Config)
    (same : canonicalLaw currentProfile current = canonicalLaw donorProfile donor)
    (event : graph.EventId) (ready : current.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (value : L.Val payload)
    (published : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
      donor.store = some (.success value)) :
    binding.get? current.store = some (.success value) ∧
      GuardCheck.allAccepted? checks current.store (.success value) = some true := by
  obtain ⟨key, member⟩ := (canonicalLaw currentProfile current).support_nonempty
  obtain ⟨left, leftMember, leftKey⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have other : key ∈ (canonicalLaw donorProfile donor).support := by rwa [← same]
  obtain ⟨right, rightMember, rightKey⟩ := (PMF.mem_support_map_iff _ _ _).mp other
  have keys : runKey left = runKey right := leftKey.trans rightKey.symm
  have leftPath := runPlan_graph_steps (graph.policyPlan currentProfile graph.canonicalScheduler)
    current.remaining current left leftMember
  have rightPath := runPlan_graph_steps (graph.policyPlan donorProfile graph.canonicalScheduler)
    donor.remaining donor right rightMember
  let field : FieldRef graph.layout (.publication payload) := ⟨.inr event, outputEq⟩
  have publishedRight : field.get? right.store = some (.success value) :=
    field.get?_preserved donor.store right.store
      (fun selected stored present => Config.Step.path_store_of_some rightPath selected stored
        present) (.success value) published
  have publishedLeft : field.get? left.store = some (.success value) :=
    (field.get?_congr left.store right.store
      (congrArg (fun image => image.2.1 (.inr event)) keys)).trans publishedRight
  have leftReach := Config.Step.path_reachable leftPath reachable
  have stored := leftReach.publication_binding event owner payload binding checks outputEq codeEq
    value publishedLeft
  have passed := leftReach.publication_guards event owner payload binding checks outputEq codeEq
    value publishedLeft
  have read : binding.field ∈ (graph.nodes event).readFields := by
    rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
    exact Finset.mem_insert_self _ _
  obtain ⟨storedValue, found⟩ := Option.isSome_iff_exists.mp (current.read_available ready read)
  have bindingEq : binding.get? current.store = binding.get? left.store := by
    apply FieldRef.get?_congr
    rw [found, Config.Step.path_store_of_some leftPath binding.field storedValue found]
  refine ⟨bindingEq.trans stored, ?_⟩
  rw [Config.publication_guards_retained event owner payload binding checks outputEq codeEq
    current left (fun _ member => ready.2 member)
    (fun selected stored present => Config.Step.path_store_of_some leftPath selected stored
      present) (.success value)]
  exact passed

/-- A completed binding of a still-active owner retains its submitted action and value. -/
theorem Config.Step.path_active_binding_record
    {origin final : graph.Config} (path : Relation.ReflTransGen Config.Step origin final)
    (event : graph.EventId) (pending : event ∉ origin.cut.completed)
    (completed : event ∈ final.cut.completed) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (active : owner ∉ final.defaulted) :
    ∃ result : PublicationResult (L.Val payload),
      completionOf final event = some (EventGraph.completion graph event
        (some (cast (congrArg EventField.Action binding.symm) (some result)))
        (cast (congrArg EventField.Value binding.symm) result)) ∧
      final.outputs event = some (cast (congrArg EventField.Value binding.symm) result) := by
  obtain ⟨current, next, ready, action, _value, _prefix, moved, suffix, _record, _stored⟩ :=
    Config.Step.path_at_completion path event pending completed
  have codeEq : cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) =
      .bind owner payload := by
    generalize cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) = code
    cases code
    rfl
  have owned : (graph.nodes event).actor = some owner :=
    (EventCode.actor_cast binding (graph.nodes event)).symm.trans (by rw [codeEq]; rfl)
  have beforeActive : owner ∉ current.defaulted := fun bad => active
    (Config.Step.path_defaulted_mono
      ((Relation.ReflTransGen.single ⟨event, ready, action, moved⟩).trans suffix) bad)
  let choice := cast (congrArg EventField.Action binding) action
  have actionEq : action = cast (congrArg EventField.Action binding.symm) choice := by
    simp only [choice, cast_cast, cast_eq]
  have law := current.step_eq_map_of_code event ready binding (.bind owner payload) codeEq
    choice (PMF.pure (choice.getD .failure)) (by
      simp only [EventCode.effectiveAction, EventCode.actor, ite_eq_right beforeActive,
        EventCode.eval?])
  rw [actionEq, law, PMF.pure_map, PMF.mem_support_pure_iff] at moved
  subst next
  cases chosen : choice with
  | none =>
      exfalso
      apply active
      apply Config.Step.path_defaulted_mono suffix
      change owner ∈ (current.complete event ready
        (cast (congrArg EventField.Action binding.symm) choice)
        (cast (congrArg EventField.Value binding.symm) (choice.getD .failure))).defaults.defaulted
      rw [chosen, Config.complete_defaults,
        current.completion_bind_none_defaultEvent event owner payload binding codeEq,
        ite_eq_right beforeActive, DefaultHistory.defaulted_record_some]
      exact Finset.mem_insert_self _ _
  | some result =>
      refine ⟨result, ?_, ?_⟩
      · apply Config.Step.path_completionOf_of_some suffix event _
        rw [completionOf_complete, Function.update_self,
          current.actualDecision_of_active event owner owned beforeActive]
        simp only [chosen, Option.getD_some]
      · apply Config.Step.path_store_of_some suffix (.inr event) _
        simpa only [Config.store_output, chosen, Option.getD_some] using
          current.complete_output_same event ready
            (cast (congrArg EventField.Action binding.symm) choice)
            (cast (congrArg EventField.Value binding.symm) (choice.getD .failure))

end Vegas.EventGraph
