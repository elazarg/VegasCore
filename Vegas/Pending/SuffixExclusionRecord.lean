/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionPublicRecord
import Vegas.Pending.ExclusionSameConfiguration
import Vegas.Pending.PhaseCompletion

/-! # Public exclusion evidence relative to a saved semantic frontier

The saved excluded set already accounts for retired attempts. Subsequent
exclusion has an actual new public failure at or after the saved source rank;
accepted unusable bindings remain outside this detector.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A saved prefix accounts for inherited exclusions, while every new excluded
owner has public evidence in the remaining source suffix. -/
structure SuffixExclusionRecord (low : Nat) (inherited : Finset Player)
    (state : RecoveryState graph) : Prop where
  receipts : state.native.ReceiptsComplete
  below : ∀ event : graph.EventId, event.val < low →
    event ∈ state.native.config.cut.completed
  excluded : ∀ owner, owner ∈ state.excluded ↔ owner ∈ inherited ∨
    ∃ event : graph.EventId, low ≤ event.val ∧ graph.actor? event = some owner ∧
      state.native.PublicFailure event

namespace SuffixExclusionRecord

variable {low : Nat} {inherited : Finset Player} {state : RecoveryState graph}

omit [DecidableEq Player] in
/-- At an exact saved prefix, no later native event can already witness a failure. -/
theorem of_prefix (receipts : state.native.ReceiptsComplete)
    (atPrefix : state.native.config.cut.IsPrefix low) (excluded : state.excluded = inherited) :
    SuffixExclusionRecord low inherited state := by
  refine ⟨receipts, fun event lower => (atPrefix.2 event).mpr lower, fun owner => ?_⟩
  rw [excluded]
  constructor
  · exact Or.inl
  · rintro (member | ⟨event, lower, _acting, failed⟩)
    · exact member
    · have earlier := (atPrefix.2 event).mp failed.completed
      omega

omit [DecidableEq Player] in
private theorem advance (valid : SuffixExclusionRecord low inherited state)
    (native : State graph) (excluded : Finset Player) (step : CompletionStep state.native native)
    (old : state.excluded ⊆ excluded)
    (newEvidence : ∀ event, event ∉ state.native.config.cut.completed →
      native.PublicFailure event → ∀ owner, graph.actor? event = some owner → owner ∈ excluded)
    (newMembers : ∀ owner ∈ excluded, owner ∈ state.excluded ∨
      ∃ event, low ≤ event.val ∧ graph.actor? event = some owner ∧ native.PublicFailure event) :
    SuffixExclusionRecord low inherited ⟨native, excluded⟩ := by
  classical
  refine ⟨valid.receipts.step step, ?_, fun owner => ⟨?_, ?_⟩⟩
  · intro event lower
    exact step.completed_mono (valid.below event lower)
  · intro member
    rcases newMembers owner member with previous | witness
    · rcases (valid.excluded owner).mp previous with inheritedOwner | ⟨query, lower, acting,
        failed⟩
      · exact Or.inl inheritedOwner
      right
      refine ⟨query, lower, acting, ?_⟩
      rcases step with ⟨same, acceptedEq, _⟩ | ⟨event, ready, action, supported, _, acceptedOnly⟩
      · exact (State.PublicFailure.congr query (by rw [same])
          (by rw [same]) (congrFun acceptedEq _)).mpr failed
      · have different : query ≠ event := fun same => ready.1 (same ▸ failed.completed)
        exact (State.PublicFailure.of_step_of_ne supported (fun field changed =>
          (acceptedOnly field changed).2) different).mpr failed
    · exact Or.inr witness
  · rintro (inheritedOwner | ⟨query, lower, acting, failed⟩)
    · exact old ((valid.excluded owner).mpr (Or.inl inheritedOwner))
    by_cases completed : query ∈ state.native.config.cut.completed
    · apply old
      apply (valid.excluded owner).mpr
      right
      refine ⟨query, lower, acting, ?_⟩
      rcases step with ⟨same, acceptedEq, _⟩ | ⟨event, ready, action, supported, _, acceptedOnly⟩
      · exact (State.PublicFailure.congr query (by rw [same])
          (by rw [same]) (congrFun acceptedEq _)).mp failed
      · have different : query ≠ event := fun same => ready.1 (same ▸ completed)
        exact (State.PublicFailure.of_step_of_ne supported (fun field changed =>
          (acceptedOnly field changed).2) different).mp failed
    · exact newEvidence query completed failed owner acting

omit [DecidableEq Player] in
theorem new_event_eq {before after : State graph} {event : graph.EventId}
    {ready : before.config.cut.Ready event} {action : graph.Action event}
    (member : after.config ∈ (before.config.step event ready action).support)
    {query : graph.EventId} (unfinished : query ∉ before.config.cut.completed)
    (completed : query ∈ after.config.cut.completed) : query = event := by
  rw [before.config.step_cut event ready action after.config member,
    EventOrder.Cut.mem_complete] at completed
  exact completed.resolve_right unfinished

omit [DecidableEq Player] in
theorem failureCompletionStep (native : State graph) (event : graph.EventId)
    (ready : native.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    CompletionStep native (native.completeFailure event ready) := by
  obtain ⟨action, member⟩ := native.completeFailure_step event ready acting
  refine Or.inr ⟨event, ready, action, member,
    native.completeFailure_activated event ready acting, ?_⟩
  intro field changed
  exact (changed (congrFun (native.completeFailure_tables event ready).1 field)).elim

omit [DecidableEq Player] in
theorem completeFailure_publicFailure (native : State graph)
    (valid : native.ReceiptsComplete) (event : graph.EventId)
    (ready : native.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    (native.completeFailure event ready).PublicFailure event := by
  cases view : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have notOwned : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [notOwned] at acting
      cases acting
  | bind actor payload outputEq codeEq =>
      left
      simpa only [State.completeFailure, view] using
        native.missedBinding_complete event ready _ _ actor payload outputEq
          (valid.vacant ready.1)
  | resolve actor payload binding checks outputEq codeEq =>
      right
      simp [RecoveryState.publicationFailed, State.completeFailure, view, State.complete]

omit [DecidableEq Player] in
/-- Automatic completion records failures only for owners already excluded. -/
theorem completeAutomatic (valid : SuffixExclusionRecord low inherited state)
    (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    SuffixExclusionRecord low inherited (state.completeAutomatic event eligible) := by
  obtain ⟨owner, acting, excluded⟩ := eligible.owned
  apply valid.advance _ state.excluded (failureCompletionStep state.native event eligible.1 acting)
    (fun _ member => member) ?_ (fun _ member => Or.inl member)
  intro query unfinished failed who owned
  have same := new_event_eq
    (Classical.choose_spec (state.native.completeFailure_step event eligible.1 acting))
    unfinished failed.completed
  subst query
  have ownerEq : owner = who := Option.some.inj (acting.symm.trans owned)
  exact ownerEq ▸ excluded

/-- Accepted bindings cannot create omission evidence; accepted openings add
exactly the owner whose public resolution failed. -/
theorem inclusionResult (valid : SuffixExclusionRecord low inherited state)
    (runtime : EventGraphRuntime graph)
    (message : Message Player (Payload graph)) (native : State graph)
    (accepted : handle runtime state.native message = some native) :
    SuffixExclusionRecord low inherited (state.inclusionResult message.payload native) := by
  have footprint := completionStep_handle runtime state.native native message accepted
  obtain ⟨event, named, ready, action, member⟩ :=
    handle_config_mem_step runtime state.native native message accepted
  apply valid.advance native _ footprint
    (state.inclusionResult_excluded_subset message.payload native) ?_ ?_
  · intro query unfinished failed owner acting
    have queryEq : query = event := new_event_eq member unfinished failed.completed
    subst query
    rcases message with ⟨id, packet⟩
    cases packet with
    | malformed => simp [Payload.event?] at named
    | commitment actual candidate =>
        have actualEq : actual = event := Option.some.inj named
        subst actual
        obtain ⟨_, _, actor, payload, outputEq, codeEq, view, _⟩ :=
          handle_commitment_conditions runtime state.native native id event candidate accepted
        have bound := (handle_commitment_tables runtime state.native native id event candidate
          accepted).2.1
        have present : native.accepted (.inr event) = some candidate := by
          rw [bound, Function.update_self]
        rcases failed with missed | publication
        · rw [native.publicView.missedBinding_of_accepted event candidate present] at missed
          cases missed
        · simp only [RecoveryState.publicationFailed, view, Bool.false_eq_true] at publication
    | opening actual candidate raw =>
        have actualEq : actual = event := Option.some.inj named
        subst actual
        obtain ⟨_, _, actor, payload, binding, checks, outputEq, codeEq, view, _⟩ :=
          handle_opening_conditions runtime state.native native id event candidate raw accepted
        have publication : RecoveryState.publicationFailed native event = true := by
          rcases failed with missed | publication
          · simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missed
          · exact publication
        change owner ∈ (if RecoveryState.publicationFailed native event then
          RecoveryState.excludeEvent state.excluded event else state.excluded)
        simp only [publication, ↓reduceIte, RecoveryState.excludeEvent, acting,
          Finset.mem_insert_self]
  · intro owner excluded
    rcases message with ⟨id, packet⟩
    cases packet with
    | malformed | commitment => exact Or.inl excluded
    | opening actual candidate raw =>
        change owner ∈ (if RecoveryState.publicationFailed native actual then
          RecoveryState.excludeEvent state.excluded actual else state.excluded) at excluded
        split at excluded
        · rename_i failed
          cases acting : graph.actor? actual with
          | none =>
              apply Or.inl
              simpa only [RecoveryState.excludeEvent, acting] using excluded
          | some actor =>
              simp only [RecoveryState.excludeEvent, acting, Finset.mem_insert] at excluded
              rcases excluded with rfl | previous
              · exact Or.inr ⟨actual, by
                  have same : actual = event := Option.some.inj named
                  subst actual
                  by_contra below
                  exact ready.1 (valid.below event (by omega)), acting, Or.inr failed⟩
              · exact Or.inl previous
        · exact Or.inl excluded

omit [DecidableEq Player] in
theorem expire_publicFailure (runtime : EventGraphRuntime graph)
    (native next : State graph) (valid : native.ReceiptsComplete) (event : graph.EventId)
    (reached : next ∈ (environmentStep runtime native (.expire event)).support)
    (changed : next.config ≠ native.config) {owner : Player}
    (acting : graph.actor? event = some owner) :
    next.PublicFailure event := by
  obtain same | ⟨ready, action, member⟩ :=
    environmentStep_expire_config_eq_or_mem_step runtime native next event reached
  · exact (changed same).elim
  have due : ∃ entered, native.activatedAt event = some entered ∧
      runtime.deadline event ≤ native.clock - entered := by
    cases activated : native.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated runtime _ event ready activated,
          PMF.mem_support_pure_iff] at reached
        exact (changed (by rw [reached])).elim
    | some entered =>
        by_cases late : runtime.deadline event ≤ native.clock - entered
        · exact ⟨entered, rfl, late⟩
        · rw [environmentStep_expire_of_not_due runtime _ event ready entered activated late,
            PMF.mem_support_pure_iff] at reached
          exact (changed (by rw [reached])).elim
  obtain ⟨entered, activated, late⟩ := due
  have nextEq : next = native.completeFailure event ready := by
    cases view : nodeView graph event with
    | sample payload law outputEq codeEq =>
        have notOwned : graph.actor? event = none :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        rw [notOwned] at acting
        cases acting
    | bind actor payload outputEq codeEq =>
        rw [environmentStep_expire_bind_eq runtime native event ready entered activated late actor
          payload outputEq codeEq view, PMF.mem_support_pure_iff] at reached
        simpa only [State.completeFailure, view] using reached
    | resolve actor payload binding checks outputEq codeEq =>
        rw [environmentStep_expire_resolve_eq runtime native event ready entered activated late
          actor payload binding checks outputEq codeEq view, PMF.mem_support_pure_iff] at reached
        simpa only [State.completeFailure, view] using reached
  rw [nextEq]
  exact completeFailure_publicFailure native valid event ready acting


/-- Native scheduler evolution records exactly its newly failed owner. -/
theorem environmentResult (valid : SuffixExclusionRecord low inherited state)
    (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime state.native command).support) :
    SuffixExclusionRecord low inherited (state.environmentResult command native) := by
  apply valid.advance native _ (completionStep_environmentStep runtime state.native native command
    reached) (state.environmentResult_excluded_subset command native) ?_ ?_
  · intro query unfinished failed owner acting
    cases command with
    | advanceClock =>
        simp only [environmentStep, PMF.mem_support_pure_iff] at reached
        subst native
        exact (unfinished failed.completed).elim
    | executeSample event =>
        rcases (environmentStep_executeSample_config_activated runtime state.native native event
          reached).2 with ⟨same, _⟩ | ⟨ready, action, member, _⟩
        · exact (unfinished (same ▸ failed.completed)).elim
        · have queryEq := new_event_eq member unfinished failed.completed
          subst query
          cases view : nodeView graph event with
          | sample payload law outputEq codeEq =>
              rcases failed with missed | publication
              · simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missed
              · simp only [RecoveryState.publicationFailed, view, Bool.false_eq_true] at publication
          | bind | resolve =>
              have nonsample : ∀ payload law outputEq codeEq,
                  nodeView graph event ≠ .sample payload law outputEq codeEq := by
                intro payload law outputEq codeEq same
                rw [view] at same
                cases same
              rw [environmentStep_executeSample_of_nonsample runtime state.native event ready
                nonsample, PMF.mem_support_pure_iff] at reached
              subst native
              exact (unfinished failed.completed).elim
    | expire event =>
        rcases environmentStep_expire_config_eq_or_mem_step runtime state.native native event
          reached with same | ⟨ready, action, member⟩
        · exact (unfinished (same ▸ failed.completed)).elim
        · have queryEq := new_event_eq member unfinished failed.completed
          subst query
          change owner ∈ (if event ∉ state.native.config.cut.completed ∧
            event ∈ native.config.cut.completed then
              RecoveryState.excludeEvent state.excluded event else state.excluded)
          simp [RecoveryState.excludeEvent, acting, unfinished, failed.completed]
  · intro owner excluded
    cases command with
    | advanceClock | executeSample => exact Or.inl excluded
    | expire event =>
        change owner ∈ (if event ∉ state.native.config.cut.completed ∧
          event ∈ native.config.cut.completed then
            RecoveryState.excludeEvent state.excluded event else state.excluded) at excluded
        split at excluded
        · rename_i completed
          cases acting : graph.actor? event with
          | none =>
              apply Or.inl
              simpa only [RecoveryState.excludeEvent, acting] using excluded
          | some actor =>
              simp only [RecoveryState.excludeEvent, acting, Finset.mem_insert] at excluded
              rcases excluded with rfl | previous
              · have changed : native.config ≠ state.native.config := by
                  intro same
                  rw [same] at completed
                  exact completed.1 completed.2
                exact Or.inr ⟨event, by
                  by_contra below
                  exact completed.1 (valid.below event (by omega)), acting,
                  expire_publicFailure runtime state.native native
                  valid.receipts event reached changed acting⟩
              · exact Or.inl previous
        · exact Or.inl excluded

theorem submit (valid : SuffixExclusionRecord low inherited state) (who : Player)
    (submission : WitnessedSubmission graph) :
    SuffixExclusionRecord low inherited (state.submit who submission) := by
  have configEq : (state.submit who submission).native.config = state.native.config := by
    change (submitStep _ who _).config = _
    rw [submitStep_config, (submission.call.register_facts who state.native).1]
  have same := (submitStep_publicView (submission.call.register state.native who) who
    submission.call.packet).trans (submission.call.register_facts who state.native).2
  apply valid.advance _ _ (Or.inl ⟨configEq, congrArg PublicView.accepted same,
    congrArg PublicView.activatedAt same⟩) (fun _ member => member) ?_
    (fun _ member => Or.inl member)
  intro event unfinished failed owner acting
  exact (unfinished (configEq ▸ failed.completed)).elim


/-- Local automatic service preserves evidence relative to the same saved rank. -/
theorem phase_drainFuel (phase : RuntimePhase graph) (fuel : Nat)
    (valid : SuffixExclusionRecord low inherited state) :
    SuffixExclusionRecord low inherited (phase.drainFuel fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      unfold RuntimePhase.drainFuel
      split
      · rename_i pending
        exact ih (valid.completeAutomatic (Classical.choose pending)
          (Classical.choose_spec pending).2)
      · exact valid

theorem phase_drain (phase : RuntimePhase graph)
    (valid : SuffixExclusionRecord low inherited state) :
    SuffixExclusionRecord low inherited (phase.drain state) :=
  valid.phase_drainFuel phase _

omit [DecidableEq Player] in
/-- At a completed binding interval, the only new exclusion evidence is an
actual absent receipt, independent of hidden typed binding failures. -/
theorem commitment_owners (phase : RuntimePhase graph) (kind : phase.kind = .commitment)
    (valid : SuffixExclusionRecord phase.low inherited state)
    (within : state.native.config.cut.Within phase.low phase.high) (who : Player) :
    who ∈ state.excluded ↔ who ∈ inherited ∨
      ∃ event ∈ phase.events, event ∈ state.native.config.cut.completed ∧
        state.native.accepted (.inr event) = none ∧ graph.actor? event = some who := by
  classical
  rw [valid.excluded who]
  constructor
  · rintro (previous | ⟨event, lower, acting, failed⟩)
    · exact Or.inl previous
    have completed := failed.completed
    have upper := within.2 event completed
    have binding := phase.fields event lower upper
    rw [kind] at binding
    obtain ⟨owner, payload, outputEq⟩ := binding
    have omitted : state.native.publicView.missedBinding event = true := by
      rcases failed with omitted | publication
      · exact omitted
      · cases view : nodeView graph event with
        | bind => simp only [RecoveryState.publicationFailed, view, Bool.false_eq_true]
            at publication
        | resolve author ty ref checks layout code => cases outputEq.symm.trans layout
        | sample ty law layout code => cases outputEq.symm.trans layout
    exact Or.inr ⟨event, (phase.mem_events event).mpr ⟨lower, upper⟩, completed,
      ((State.publicView_missedBinding state.native event owner payload outputEq).mp omitted).2,
      acting⟩
  · rintro (previous | ⟨event, inside, completed, absent, acting⟩)
    · exact Or.inl previous
    obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
    have binding := phase.fields event lower upper
    rw [kind] at binding
    obtain ⟨owner, payload, outputEq⟩ := binding
    exact Or.inr ⟨event, lower, acting, Or.inl
      ((State.publicView_missedBinding state.native event owner payload outputEq).mpr
        ⟨completed, absent⟩)⟩

end SuffixExclusionRecord
end Vegas.EventGraphRuntime
