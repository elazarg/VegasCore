/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PublicFailureEvidence

/-! # Exact exclusion evidence relative to a saved semantic frontier

Inherited exclusions account for retired attempts. Every later exclusion is
witnessed by an owned public failure at or above the saved source rank. The
zero frontier with empty inheritance gives the ordinary permanent exclusion law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A saved prefix accounts for inherited exclusions, while every new excluded
owner has public evidence in the remaining source suffix. -/
structure ExclusionEvidence (low : Nat) (inherited : Finset Player)
    (state : RecoveryState graph) : Prop where
  receipts : state.native.ReceiptsComplete
  below : ∀ event : graph.EventId, event.val < low →
    event ∈ state.native.config.cut.completed
  excluded : ∀ owner, owner ∈ state.excluded ↔ owner ∈ inherited ∨
    ∃ event : graph.EventId, low ≤ event.val ∧ graph.actor? event = some owner ∧
      state.native.PublicFailure event

namespace ExclusionEvidence

variable {low : Nat} {inherited : Finset Player} {state : RecoveryState graph}

omit [DecidableEq Player] in
/-- At an exact saved prefix, no later native event can already witness a failure. -/
theorem of_rank_cut (receipts : state.native.ReceiptsComplete)
    (atPrefix : ∀ event : graph.EventId,
      event ∈ state.native.config.cut.completed ↔ event.val < low)
    (excluded : state.excluded = inherited) :
    ExclusionEvidence low inherited state := by
  refine ⟨receipts, fun event lower => (atPrefix event).mpr lower, fun owner => ?_⟩
  rw [excluded]
  constructor
  · exact Or.inl
  · rintro (member | ⟨event, lower, _acting, failed⟩)
    · exact member
    · have earlier := (atPrefix event).mp failed.completed
      omega

omit [DecidableEq Player] in
private theorem advance (valid : ExclusionEvidence low inherited state)
    (native : State graph) (excluded : Finset Player) (step : CompletionStep state.native native)
    (old : state.excluded ⊆ excluded)
    (newEvidence : ∀ event, event ∉ state.native.config.cut.completed →
      native.PublicFailure event → ∀ owner, graph.actor? event = some owner → owner ∈ excluded)
    (newMembers : ∀ owner ∈ excluded, owner ∈ state.excluded ∨
      ∃ event, low ≤ event.val ∧ graph.actor? event = some owner ∧ native.PublicFailure event) :
    ExclusionEvidence low inherited ⟨native, excluded⟩ := by
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
      exact (step.publicFailure_iff_of_completed failed.completed).mpr failed
    · exact Or.inr witness
  · rintro (inheritedOwner | ⟨query, lower, acting, failed⟩)
    · exact old ((valid.excluded owner).mpr (Or.inl inheritedOwner))
    by_cases completed : query ∈ state.native.config.cut.completed
    · apply old
      apply (valid.excluded owner).mpr
      right
      refine ⟨query, lower, acting, ?_⟩
      exact (step.publicFailure_iff_of_completed completed).mp failed
    · exact newEvidence query completed failed owner acting

omit [DecidableEq Player] in
/-- A native completion footprint with unchanged configuration preserves the
entire evidence family at the same saved frontier. -/
theorem completionStep_sameConfig {before after : State graph} {excluded : Finset Player}
    (valid : ExclusionEvidence low inherited (RecoveryState.mk before excluded))
    (step : CompletionStep before after) (same : after.config = before.config) :
    ExclusionEvidence low inherited (RecoveryState.mk after excluded) := by
  apply valid.advance after excluded step (fun _ member => member) ?_
    (fun _ member => Or.inl member)
  intro event unfinished failed _owner _acting
  exact (unfinished (same ▸ failed.completed)).elim

omit [DecidableEq Player] in
/-- Automatic completion records failures only for owners already excluded. -/
theorem completeAutomatic (valid : ExclusionEvidence low inherited state)
    (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    ExclusionEvidence low inherited (state.completeAutomatic event eligible) := by
  obtain ⟨owner, acting, excluded⟩ := eligible.owned
  apply valid.advance _ state.excluded
    (State.completeFailure_completionStep state.native event eligible.1 acting)
    (fun _ member => member) ?_ (fun _ member => Or.inl member)
  intro query unfinished failed who owned
  have same := State.completed_event_eq_of_step
    (Classical.choose_spec (state.native.completeFailure_step event eligible.1 acting))
    unfinished failed.completed
  subst query
  have ownerEq : owner = who := Option.some.inj (acting.symm.trans owned)
  exact ownerEq ▸ excluded

/-- Accepted bindings cannot create omission evidence; accepted openings add
exactly the owner whose public resolution failed. -/
theorem inclusionResult (valid : ExclusionEvidence low inherited state)
    (runtime : EventGraphRuntime graph)
    (message : Message Player (Payload graph)) (native : State graph)
    (accepted : handle runtime state.native message = some native) :
    ExclusionEvidence low inherited (state.inclusionResult message.payload native) := by
  have footprint := completionStep_handle runtime state.native native message accepted
  obtain ⟨event, named, ready, action, member⟩ :=
    handle_config_mem_step runtime state.native native message accepted
  apply valid.advance native _ footprint
    (state.inclusionResult_excluded_subset message.payload native) ?_ ?_
  · intro query unfinished failed owner acting
    have queryEq : query = event :=
      State.completed_event_eq_of_step member unfinished failed.completed
    subst query
    rcases message with ⟨id, packet⟩
    cases packet with
    | malformed => simp [Payload.event?] at named
    | commitment actual candidate =>
        have actualEq : actual = event := Option.some.inj named
        subst actual
        obtain ⟨_, _, actor, payload, outputEq, codeEq, view, _⟩ :=
          (handle_commitment_iff runtime state.native native id event candidate).mp accepted
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
          (handle_opening_iff runtime state.native native id event candidate raw).mp accepted
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
  exact State.completeFailure_publicFailure native valid event ready acting

/-- Native scheduler evolution records exactly its newly failed owner. -/
theorem environmentResult (valid : ExclusionEvidence low inherited state)
    (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime state.native command).support) :
    ExclusionEvidence low inherited (state.environmentResult command native) := by
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
        · have queryEq := State.completed_event_eq_of_step member unfinished failed.completed
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
        · have queryEq := State.completed_event_eq_of_step member unfinished failed.completed
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

theorem submit (valid : ExclusionEvidence low inherited state) (who : Player)
    (submission : WitnessedSubmission graph) :
    ExclusionEvidence low inherited (state.submit who submission) := by
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

omit [DecidableEq Player] in
/-- With no inherited frontier, exact evidence is just an owned public failure. -/
theorem excluded_zero {state : RecoveryState graph}
    (valid : ExclusionEvidence 0 ∅ state) (owner : Player) :
    owner ∈ state.excluded ↔
      ∃ event, graph.actor? event = some owner ∧ state.native.PublicFailure event := by
  simpa using valid.excluded owner

/-- The initial state has no completed failures or inherited exclusions. -/
theorem initial (inputs : graph.Inputs) :
    ExclusionEvidence 0 ∅ (⟨State.initial inputs, ∅⟩ : RecoveryState graph) := by
  refine ⟨State.ReceiptsComplete.initial inputs, fun event lower => by omega,
    fun owner => ⟨?_, ?_⟩⟩
  · intro member
    exact (Finset.notMem_empty owner member).elim
  · rintro (inheritedOwner | ⟨event, _, _, failed⟩)
    · exact inheritedOwner
    · have completed := failed.completed
      simp [State.initial, EventGraph.Config.initial, EventOrder.Cut.empty] at completed

omit [DecidableEq Player] in
/-- Equal public native views determine equal exclusions at a shared frontier. -/
theorem excluded_eq_of_publicView_eq {other : RecoveryState graph}
    (valid : ExclusionEvidence low inherited state)
    (otherValid : ExclusionEvidence low inherited other)
    (same : state.native.publicView = other.native.publicView) :
    state.excluded = other.excluded := by
  classical
  ext owner
  rw [valid.excluded owner, otherValid.excluded owner]
  constructor
  · rintro (member | ⟨event, lower, acting, failed⟩)
    · exact Or.inl member
    · exact Or.inr ⟨event, lower, acting,
        (State.PublicFailure.of_publicView_eq same event).mp failed⟩
  · rintro (member | ⟨event, lower, acting, failed⟩)
    · exact Or.inl member
    · exact Or.inr ⟨event, lower, acting,
        (State.PublicFailure.of_publicView_eq same event).mpr failed⟩

/-- The full automatic drain preserves exact public exclusion evidence. -/
theorem drainFuel (fuel : Nat) (valid : ExclusionEvidence low inherited state) :
    ExclusionEvidence low inherited (RecoveryState.drainFuel fuel state) := by
  exact RecoveryState.drainFuel_induction (ExclusionEvidence low inherited)
    (fun _ event eligible previous => previous.completeAutomatic event eligible) fuel state valid

theorem drain (valid : ExclusionEvidence low inherited state) :
    ExclusionEvidence low inherited state.drain :=
  valid.drainFuel _

theorem handle (valid : ExclusionEvidence low inherited state) (runtime : EventGraphRuntime graph)
    (message : Message Player (WitnessedPacket graph)) (next : RecoveryState graph)
    (accepted : state.handle runtime message = some next) :
    ExclusionEvidence low inherited next := by
  unfold RecoveryState.handle at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact (valid.inclusionResult runtime _ native rawAccepted).drain
    · cases accepted

theorem environment (valid : ExclusionEvidence low inherited state)
    (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (next : RecoveryState graph)
    (reached : next ∈ (state.environment runtime command).support) :
    ExclusionEvidence low inherited next := by
  rw [RecoveryState.environment, PMF.support_map] at reached
  obtain ⟨native, realized, rfl⟩ := reached
  exact (valid.environmentResult runtime command native realized).drain

end ExclusionEvidence
end Vegas.EventGraphRuntime
