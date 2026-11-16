module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.CanonicalPrefix
public import Vegas.EventGraph.ResolutionProvenance
public import Vegas.EventGraph.PrefixRestriction
public import Vegas.EventGraph.Recall
public import Vegas.EventGraph.PrefixReplay

@[expose] public section

/-! # Binding observations across partially completed private runs

Source-prefix observations agree when a binding decision has the same earlier
own records along paths from a common rank-prefix boundary. Foreign private
completions may differ in values and order. Visible stores and public defaults
are derived from the paths and retained information barriers.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Earlier own completion records determine the prefix action history. -/
theorem prefixOwnActions_eq_of_records
    (who : Player) (event : graph.EventId) (left right : graph.Config)
    (records : ∀ prior : graph.EventId, prior.val < event.val →
      graph.actor? prior = some who → completionOf left prior = completionOf right prior) :
    (graph.prefixObservation who event (graph.playerObserve who left)).ownActions =
      (graph.prefixObservation who event (graph.playerObserve who right)).ownActions := by
  change ((graph.normalizeObservation who (graph.playerObserve who left)).ownActions.filter
      (fun completion => completion.event.val < event.val)) =
    ((graph.normalizeObservation who (graph.playerObserve who right)).ownActions.filter
      (fun completion => completion.event.val < event.val))
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve]
  simp only [List.filter_filterMap]
  congr 1
  funext prior
  by_cases earlier : prior.val < event.val
  · by_cases owned : graph.actor? prior = some who
    · rw [records prior earlier owned]
    · have absent (config : graph.Config) :
          ((completionOf config prior).filter (fun completion =>
            graph.actor? completion.event = some who ∧ completion.decision.isSome)).filter
            (fun completion => completion.event.val < event.val) = none := by
        apply Option.filter_eq_none_iff.mpr
        intro completion found
        have tagged := completionOf_filter_tagged config _ prior completion found
        obtain ⟨_, chosen⟩ := Option.filter_eq_some_iff.mp found
        apply (owned _).elim
        simpa only [tagged] using (of_decide_eq_true chosen).1
      rw [absent left, absent right]
  · have absent (config : graph.Config) :
        ((completionOf config prior).filter (fun completion =>
          graph.actor? completion.event = some who ∧ completion.decision.isSome)).filter
          (fun completion => completion.event.val < event.val) = none := by
      apply Option.filter_eq_none_iff.mpr
      intro completion found later
      have tagged := completionOf_filter_tagged config _ prior completion found
      exact earlier (by simpa only [tagged, decide_eq_true_eq] using later)
    rw [absent left, absent right]

/-- Prefix default slots depend only on the earlier public completion records. -/
theorem prefixDefaults_eq_of_records
    (who : Player) (event : graph.EventId) (left right : graph.Config)
    (records : ∀ prior : graph.EventId, prior.val < event.val →
      (graph.outputLayout prior).IsPublic →
        (completionOf left prior).bind EventCompletion.defaultEvent =
          (completionOf right prior).bind EventCompletion.defaultEvent) :
    (graph.prefixObservation who event (graph.playerObserve who left)).defaults =
      (graph.prefixObservation who event (graph.playerObserve who right)).defaults := by
  change DefaultHistory.mk _ = DefaultHistory.mk _
  congr 2
  apply List.map_congr_left
  intro prior member
  have earlier : prior.val < event.val := by
    simpa only [decisionPrefix, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] using member
  by_cases publicOutput : (graph.outputLayout prior).IsPublic
  · simp only [ite_eq_left publicOutput, observedDefaultOf_playerObserve,
      records prior earlier publicOutput]
  · simp only [ite_eq_right publicOutput]

theorem prefixObservation_playerObserve_of_visible_records
    (who : Player) (event : graph.EventId) (left right : graph.Config)
    (stores : ∀ field, graph.fieldVisibleTo who field → left.store field = right.store field)
    (own : ∀ prior : graph.EventId, prior.val < event.val →
      graph.actor? prior = some who → completionOf left prior = completionOf right prior)
    (defaults : ∀ prior : graph.EventId, prior.val < event.val →
      (graph.outputLayout prior).IsPublic →
        (completionOf left prior).bind EventCompletion.defaultEvent =
          (completionOf right prior).bind EventCompletion.defaultEvent) :
    graph.prefixObservation who event (graph.playerObserve who left) =
      graph.prefixObservation who event (graph.playerObserve who right) := by
  apply EventPlayerObservation.ext
  · rfl
  · exact graph.playerStore_congr who left.store right.store stores
  · exact prefixOwnActions_eq_of_records who event left right own
  · exact prefixDefaults_eq_of_records who event left right defaults

theorem RevealRelaxedOrdered.prefixOwnActions_eq_of_ready_path
    (relaxed : graph.RevealRelaxedOrdered) (who : Player) (event : graph.EventId)
    (before after : graph.Config) (ready : before.cut.Ready event)
    (owned : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (path : Relation.ReflTransGen Config.Step before after) :
    (graph.prefixObservation who event (graph.playerObserve who before)).ownActions =
      (graph.prefixObservation who event (graph.playerObserve who after)).ownActions := by
  apply prefixOwnActions_eq_of_records
  intro prior earlier actor
  have complete : prior ∈ before.cut.completed :=
    (relaxed.ready_visible_iff before.cut ready owned
      (EventCode.output_visible_of_actor (graph.nodes prior) who actor)
      (IndependentReveals.not_of_not_publication_right notPublication)
      (IndependentReveals.not_of_not_publication_left notPublication)).mpr earlier
  obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
    ((completionOf_isSome_iff before prior).mpr complete)
  exact found.trans (Config.Step.path_completionOf_of_some path prior record found).symm

theorem RevealRelaxedOrdered.prefixDefaults_eq_of_ready_path
    (relaxed : graph.RevealRelaxedOrdered) (who : Player) (event : graph.EventId)
    (before after : graph.Config) (ready : before.cut.Ready event)
    (owned : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (path : Relation.ReflTransGen Config.Step before after) :
    (graph.prefixObservation who event (graph.playerObserve who before)).defaults =
      (graph.prefixObservation who event (graph.playerObserve who after)).defaults := by
  apply prefixDefaults_eq_of_records
  intro prior earlier publicOutput
  have visible : (graph.outputLayout prior).VisibleTo who := by
    cases kind : graph.outputLayout prior <;>
      simp_all only [EventField.IsPublic, EventField.VisibleTo]
  have complete : prior ∈ before.cut.completed :=
    (relaxed.ready_visible_iff before.cut ready owned visible
      (IndependentReveals.not_of_not_publication_right notPublication)
      (IndependentReveals.not_of_not_publication_left notPublication)).mpr earlier
  obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
    ((completionOf_isSome_iff before prior).mpr complete)
  rw [found, Config.Step.path_completionOf_of_some path prior record found]

omit [DecidableEq Player] in
private theorem binding_code (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) =
      .bind owner payload := by
  generalize cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) = code
  cases code
  rfl

theorem Config.Reachable.binding_outputs_eq_of_completionOf
    {leftInputs rightInputs : graph.Inputs} {left right : graph.Config}
    (leftReach : left.Reachable leftInputs) (rightReach : right.Reachable rightInputs)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (records : completionOf left event = completionOf right event) :
    left.outputs event = right.outputs event := by
  classical
  cases found : completionOf left event with
  | none =>
      have rightFound : completionOf right event = none := records.symm.trans found
      have leftAbsent := (completionOf_eq_none_iff left event).mp found
      have rightAbsent := (completionOf_eq_none_iff right event).mp rightFound
      have absent (config : graph.Config) (missing : event ∉ config.cut.completed) :
          config.outputs event = none := by
        exact Option.not_isSome_iff_eq_none.mp fun stored =>
          missing ((config.output_available event).mp stored)
      rw [absent left leftAbsent, absent right rightAbsent]
  | some record =>
      have rightFound : completionOf right event = some record := records.symm.trans found
      have leftMember := ((completionOf_eq_some_iff left event record).mp found).1
      have rightMember := ((completionOf_eq_some_iff right event record).mp rightFound).1
      have tagged := completionOf_tagged left event record found
      subst event
      have recordBinding : graph.outputLayout record.event = .binding owner payload :=
        binding
      have leftOutput := leftReach.binding_output record leftMember owner payload recordBinding
        (binding_code _ _ _ recordBinding)
      have rightOutput := rightReach.binding_output record rightMember owner payload recordBinding
        (binding_code _ _ _ recordBinding)
      exact leftOutput.trans rightOutput.symm

theorem prefixObservation_playerObserve_of_binding_paths
    (relaxed : graph.RevealRelaxedOrdered)
    {inputs : graph.Inputs} (origin left right : graph.Config) (start : Nat)
    (originReach : origin.Reachable inputs) (ordered : origin.cut.IsPrefix start)
    (leftPath : Relation.ReflTransGen Config.Step origin left)
    (rightPath : Relation.ReflTransGen Config.Step origin right)
    (who : Player) (event : graph.EventId) (owned : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (bindings : ∀ prior : graph.EventId, start ≤ prior.val → prior.val < event.val →
      ∃ owner payload, graph.outputLayout prior = .binding owner payload)
    (own : ∀ prior : graph.EventId, prior.val < event.val →
      graph.actor? prior = some who → completionOf left prior = completionOf right prior) :
    graph.prefixObservation who event (graph.playerObserve who left) =
      graph.prefixObservation who event (graph.playerObserve who right) := by
  classical
  have reachable {current : graph.Config}
      (path : Relation.ReflTransGen Config.Step origin current) : current.Reachable inputs := by
    induction path with
    | refl => exact originReach
    | tail _ moved previous =>
        obtain ⟨next, ready, action, supported⟩ := moved
        exact .step previous next ready action _ supported
  have oldRecords (prior : graph.EventId) (earlier : prior.val < start) :
      completionOf left prior = completionOf right prior := by
    have completed : prior ∈ origin.cut.completed := (ordered.2 prior).mpr earlier
    obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
      ((completionOf_isSome_iff origin prior).mpr completed)
    rw [Config.Step.path_completionOf_of_some leftPath prior record found,
      Config.Step.path_completionOf_of_some rightPath prior record found]
  refine prefixObservation_playerObserve_of_visible_records who event left right ?_ own ?_
  · intro field visible
    cases field with
    | inl input =>
        change some (left.inputs input) = some (right.inputs input)
        rw [Config.Step.path_inputs_eq leftPath, Config.Step.path_inputs_eq rightPath]
    | inr prior =>
        change left.outputs prior = right.outputs prior
        change (graph.outputLayout prior).VisibleTo who at visible
        by_cases earlier : prior.val < event.val
        · by_cases old : prior.val < start
          · have completed : prior ∈ origin.cut.completed := (ordered.2 prior).mpr old
            obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp
              ((origin.output_available prior).mpr completed)
            exact (Config.Step.path_store_of_some leftPath (.inr prior) value found).trans
              (Config.Step.path_store_of_some rightPath (.inr prior) value found).symm
          · obtain ⟨owner, payload, binding⟩ :=
              bindings prior (Nat.le_of_not_gt old) earlier
            have ownerEq : owner = who := by
              simpa only [binding, EventField.VisibleTo] using visible
            have actor : graph.actor? prior = some who := by
              change EventCode.actor (graph.nodes prior) = some who
              rw [← EventCode.actor_cast binding (graph.nodes prior),
                binding_code prior owner payload binding]
              exact congrArg some ownerEq
            exact Config.Reachable.binding_outputs_eq_of_completionOf (reachable leftPath)
              (reachable rightPath) prior owner payload binding (own prior earlier actor)
        · have absent (current : graph.Config) (ready : current.cut.Ready event) :
              current.outputs prior = none := by
            apply Option.not_isSome_iff_eq_none.mp
            intro stored
            exact earlier ((relaxed.ready_visible_iff current.cut ready owned visible
              (IndependentReveals.not_of_not_publication_right notPublication)
              (IndependentReveals.not_of_not_publication_left notPublication)).mp
              ((current.output_available prior).mp stored))
          rw [absent left leftReady, absent right rightReady]
  · intro prior earlier publicOutput
    by_cases old : prior.val < start
    · rw [oldRecords prior old]
    · obtain ⟨owner, payload, binding⟩ := bindings prior (Nat.le_of_not_gt old) earlier
      simp only [binding, EventField.IsPublic] at publicOutput

theorem prefixProfile_actionLaw_of_binding_paths
    (relaxed : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    {inputs : graph.Inputs} (origin left right : graph.Config) (start : Nat)
    (originReach : origin.Reachable inputs) (ordered : origin.cut.IsPrefix start)
    (leftPath : Relation.ReflTransGen Config.Step origin left)
    (rightPath : Relation.ReflTransGen Config.Step origin right)
    (who : Player) (event : graph.EventId) (owned : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted)
    (bindings : ∀ prior : graph.EventId, start ≤ prior.val → prior.val < event.val →
      ∃ owner payload, graph.outputLayout prior = .binding owner payload)
    (own : ∀ prior : graph.EventId, prior.val < event.val →
      graph.actor? prior = some who → completionOf left prior = completionOf right prior) :
    actionLaw (graph.prefixProfile profile) left event =
      actionLaw (graph.prefixProfile profile) right event := by
  have same := prefixObservation_playerObserve_of_binding_paths relaxed origin left right start
    originReach ordered leftPath rightPath who event owned notPublication leftReady rightReady
    bindings own
  rw [actionLaw_of_actor _ _ owned, actionLaw_of_actor _ _ owned,
    dite_eq_right leftActive, dite_eq_right rightActive]
  change profile who event owned _ _ = profile who event owned _ _
  have congrPolicy (before after : graph.PlayerObservation who) (same : before = after)
      (beforeActive : who ∉ before.defaulted) (afterActive : who ∉ after.defaulted) :
      profile who event owned before beforeActive = profile who event owned after afterActive := by
    subst after
    rfl
  exact congrPolicy _ _ same _ _

theorem fromSequentialConfig_prefixObservation (who : Player) (event : graph.EventId)
    (config : graph.sequentialize.Config) :
    graph.prefixObservation who event
        (graph.playerObserve who (graph.fromSequentialConfig config)) =
      graph.sequentialize.prefixObservation who event
        (graph.sequentialize.playerObserve who config) := by
  apply EventPlayerObservation.ext
  · rfl
  · funext field
    cases field <;> rfl
  · rfl
  · rfl


end Vegas.EventGraph

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem ownCompletions_eq_of_records
    (relaxed : graph.RevealRelaxedOrdered)
    {leftInputs rightInputs : graph.Inputs} (left right : graph.Config)
    (leftReach : left.Reachable leftInputs) (rightReach : right.Reachable rightInputs)
    (records : completionOf left = completionOf right) (who : Player) :
    graph.ownCompletions who left.history = graph.ownCompletions who right.history := by
  classical
  let earlier : graph.Completion → graph.Completion → Prop :=
    fun first second => first.event.val < second.event.val
  let _ : Std.Antisymm earlier := ⟨fun _ _ before after => (Nat.lt_asymm before after).elim⟩
  let _ : Std.Irrefl earlier := ⟨fun record less => Nat.lt_irrefl record.event.val less⟩
  have leftOrder : (graph.ownCompletions who left.history).Pairwise earlier := by
    simpa only [ownEventIds, List.pairwise_map] using
      leftReach.ownEventIds_pairwise
        (fun {_ _ _} earlier priorOwned eventOwned =>
          relaxed.same_owner_predecessor _ _ _ earlier priorOwned eventOwned) who
  have rightOrder : (graph.ownCompletions who right.history).Pairwise earlier := by
    simpa only [ownEventIds, List.pairwise_map] using
      rightReach.ownEventIds_pairwise
        (fun {_ _ _} earlier priorOwned eventOwned =>
          relaxed.same_owner_predecessor _ _ _ earlier priorOwned eventOwned) who
  apply leftOrder.eq_of_mem_iff rightOrder
  intro record
  have present : record ∈ left.history ↔ record ∈ right.history := by
    constructor
    · intro member
      have found := (completionOf_eq_some_iff left record.event record).mpr ⟨member, rfl⟩
      rw [records] at found
      exact ((completionOf_eq_some_iff right record.event record).mp found).1
    · intro member
      have found := (completionOf_eq_some_iff right record.event record).mpr ⟨member, rfl⟩
      rw [← records] at found
      exact ((completionOf_eq_some_iff left record.event record).mp found).1
  simp only [ownCompletions, List.mem_filter, present]

theorem defaults_of_binding_path
    (origin final : graph.Config) (start finish : Nat)
    (path : Relation.ReflTransGen Config.Step origin final)
    (before : origin.cut.IsPrefix start) (after : final.cut.IsPrefix finish)
    (bindings : ∀ event : graph.EventId, start ≤ event.val → event.val < finish →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (clean : final.NoBindingDefaults) :
    final.defaults.events = List.replicate (finish - start) none ++ origin.defaults.events := by
  classical
  obtain ⟨extra, extended⟩ := Config.Step.path_history_prefix path
  have disjoint : List.Disjoint (origin.history.map EventCompletion.event)
      (extra.map EventCompletion.event) := by
    apply List.disjoint_of_nodup_append
    simpa only [← extended, List.map_append] using final.history_nodup
  have length : extra.length = finish - start := by
    have sum := congrArg List.length extended
    simp only [List.length_append] at sum
    rw [Config.history_length_of_isPrefix origin before,
      Config.history_length_of_isPrefix final after] at sum
    omega
  have noDefault : extra.map EventCompletion.defaultEvent =
      List.replicate extra.length none := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro value member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    have finalMember : record ∈ final.history := by
      rw [← extended]
      exact List.mem_append_right _ present
    have completed : record.event ∈ final.cut.completed :=
      (final.history_exact record.event).mp (List.mem_map.mpr ⟨record, finalMember, rfl⟩)
    have lower : start ≤ record.event.val := by
      by_contra notLower
      have old : record.event ∈ origin.history.map EventCompletion.event :=
        (origin.history_exact record.event).mpr ((before.2 record.event).mpr (by omega))
      exact List.disjoint_left.mp disjoint old (List.mem_map.mpr ⟨record, present, rfl⟩)
    obtain ⟨owner, payload, binding⟩ :=
      bindings record.event lower ((after.2 record.event).mp completed)
    exact clean record finalMember owner payload binding
  change (final.history.map EventCompletion.defaultEvent).reverse =
    List.replicate (finish - start) none ++
      (origin.history.map EventCompletion.defaultEvent).reverse
  rw [← extended, List.map_append, noDefault, length, List.reverse_append,
    List.reverse_replicate]

theorem store_eq_of_binding_paths
    {inputs : graph.Inputs} (origin left right : graph.Config) (start finish : Nat)
    (originReach : origin.Reachable inputs) (before : origin.cut.IsPrefix start)
    (leftPath : Relation.ReflTransGen Config.Step origin left)
    (rightPath : Relation.ReflTransGen Config.Step origin right)
    (leftOrdered : left.cut.IsPrefix finish) (rightOrdered : right.cut.IsPrefix finish)
    (bindings : ∀ event : graph.EventId, start ≤ event.val → event.val < finish →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (records : completionOf left = completionOf right) : left.store = right.store := by
  classical
  funext field
  cases field with
  | inl input =>
      change some (left.inputs input) = some (right.inputs input)
      rw [Config.Step.path_inputs_eq leftPath, Config.Step.path_inputs_eq rightPath]
  | inr event =>
      change left.outputs event = right.outputs event
      by_cases earlier : event.val < finish
      · by_cases old : event.val < start
        · have completed : event ∈ origin.cut.completed := (before.2 event).mpr old
          obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp
            ((origin.output_available event).mpr completed)
          exact (Config.Step.path_store_of_some leftPath (.inr event) value found).trans
            (Config.Step.path_store_of_some rightPath (.inr event) value found).symm
        · obtain ⟨owner, payload, binding⟩ := bindings event (Nat.le_of_not_gt old) earlier
          exact Config.Reachable.binding_outputs_eq_of_completionOf
            (Config.Step.path_reachable leftPath originReach) (Config.Step.path_reachable rightPath
              originReach) event owner payload binding
            (congrFun records event)
      · have absent (config : graph.Config) (ordered : config.cut.IsPrefix finish) :
            config.outputs event = none := by
          exact Option.not_isSome_iff_eq_none.mp fun present =>
            earlier ((ordered.2 event).mp ((config.output_available event).mp present))
        rw [absent left leftOrdered, absent right rightOrdered]

/-- A reachable binding record fixes its stored result from the requested action. -/
theorem binding_frame_of_typed_action
    {inputs : graph.Inputs} (filled : graph.Config) (reachable : filled.Reachable inputs)
    (table : (event : graph.EventId) → graph.Action event)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload))
    (actionEq : table event = cast (congrArg EventField.Action binding.symm) (some result))
    (frame : ∃ value : (graph.outputLayout event).Value,
      completionOf filled event =
          some (EventGraph.completion graph event (some (table event)) value) ∧
        filled.outputs event = some value) :
    completionOf filled event = some (EventGraph.completion graph event
        (some (cast (congrArg EventField.Action binding.symm) (some result)))
        (cast (congrArg EventField.Value binding.symm) result)) ∧
      filled.outputs event = some (cast (congrArg EventField.Value binding.symm) result) := by
  obtain ⟨value, record, stored⟩ := frame
  have member := ((completionOf_eq_some_iff filled event _).mp record).1
  have codeEq : cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) =
      .bind owner payload := by
    generalize cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) = code
    cases code
    rfl
  have physical := reachable.binding_output _ member owner payload binding codeEq
  change filled.outputs event = some (cast (congrArg EventField.Value binding.symm)
    (((some (table event)).bind fun chosen =>
      cast (congrArg EventField.Action binding) chosen).getD .failure)) at physical
  simp only [actionEq, Option.bind_some, cast_cast, cast_eq, Option.getD_some] at physical
  have valueEq := Option.some.inj (stored.symm.trans physical)
  rw [valueEq, actionEq] at record
  exact ⟨record, physical⟩

/-- Replacing only focal binding records preserves every honest prefix kernel. -/
theorem prefixProfile_actionLaw_of_cropped_binding_fill
    (relaxed : graph.RevealRelaxedOrdered) (profile : graph.BehavioralProfile)
    (focal : Player) {inputs : graph.Inputs}
    (origin donor filled : graph.Config) (start rank : Nat)
    (originReach : origin.Reachable inputs) (before : origin.cut.IsPrefix start)
    (donorPath : Relation.ReflTransGen Config.Step origin donor)
    (filledPath : Relation.ReflTransGen Config.Step origin filled)
    (donorOrdered : donor.cut.IsPrefix rank) (filledOrdered : filled.cut.IsPrefix rank)
    (donorClear : donor.defaulted = ∅) (filledClear : filled.defaulted = ∅)
    (bindings : ∀ event : graph.EventId, start ≤ event.val → event.val < rank →
      ∃ owner payload, graph.outputLayout event = .binding owner payload)
    (focalRecords : graph.EventId → Option graph.Completion)
    (records : ∀ event : graph.EventId, start ≤ event.val → event.val < rank →
      completionOf filled event = if graph.actor? event = some focal then focalRecords event
        else completionOf donor event)
    (owner : Player) (honest : owner ≠ focal) (event : graph.EventId)
    (eventRank : event.val = rank) (owned : graph.actor? event = some owner)
    (notPublication : ¬ (graph.outputLayout event).IsPublication) :
    actionLaw (graph.prefixProfile profile) filled event =
      actionLaw (graph.prefixProfile profile) donor event := by
  have inside : rank < graph.order.eventCount := by rw [← eventRank]; exact event.isLt
  have readyDonor : donor.cut.Ready event := by
    have ready := donorOrdered.ready inside
    have same : (⟨rank, inside⟩ : graph.EventId) = event := Fin.ext eventRank.symm
    exact same ▸ ready
  have readyFilled : filled.cut.Ready event := by
    have ready := filledOrdered.ready inside
    have same : (⟨rank, inside⟩ : graph.EventId) = event := Fin.ext eventRank.symm
    exact same ▸ ready
  apply prefixProfile_actionLaw_of_binding_paths relaxed profile origin filled donor start
    originReach before filledPath donorPath owner event owned notPublication readyFilled readyDonor
      (by rw [filledClear]; simp) (by rw [donorClear]; simp)
  · intro prior lower upper
    exact bindings prior lower (by omega)
  · intro prior earlier actor
    by_cases old : prior.val < start
    · have completed : prior ∈ origin.cut.completed := (before.2 prior).mpr old
      obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff origin prior).mpr completed)
      rw [Config.Step.path_completionOf_of_some filledPath prior record found,
        Config.Step.path_completionOf_of_some donorPath prior record found]
    · have different : graph.actor? prior ≠ some focal := by
        intro focalActor
        exact honest (Option.some.inj (actor.symm.trans focalActor))
      rw [records prior (by omega) (by omega), ite_eq_right different]

end Vegas.EventGraph
