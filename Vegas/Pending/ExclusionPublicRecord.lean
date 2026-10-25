/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PublicFailureEvidence
import Vegas.Pending.EventValueSwap

/-! # Permanent exclusion reconstructed from public completion records -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The permanent set is exactly the owners of public failure evidence. -/
structure PublicExclusionRecord (state : RecoveryState graph) : Prop where
  receipts : state.native.ReceiptsComplete
  excluded : ∀ owner, owner ∈ state.excluded ↔
    ∃ event, graph.actor? event = some owner ∧ state.native.PublicFailure event

namespace PublicExclusionRecord

variable {state : RecoveryState graph}

omit [DecidableEq Player] in
/-- Equal native public views determine equal permanent sets on recorded states. -/
theorem excluded_eq_of_publicView_eq {other : RecoveryState graph}
    (valid : PublicExclusionRecord state) (validOther : PublicExclusionRecord other)
    (same : state.native.publicView = other.native.publicView) :
    state.excluded = other.excluded := by
  classical
  ext owner
  rw [valid.excluded owner, validOther.excluded owner]
  constructor
  · rintro ⟨event, acting, failed⟩
    exact ⟨event, acting, (State.PublicFailure.of_publicView_eq same event).mp failed⟩
  · rintro ⟨event, acting, failed⟩
    exact ⟨event, acting, (State.PublicFailure.of_publicView_eq same event).mpr failed⟩

omit [DecidableEq Player] in
/-- A local completion can create public evidence only for its newly completed
event; all previous evidence remains recorded. -/
private theorem advance (valid : PublicExclusionRecord state)
    (native : State graph) (excluded : Finset Player) (step : CompletionStep state.native native)
    (old : state.excluded ⊆ excluded)
    (newEvidence : ∀ event, event ∉ state.native.config.cut.completed →
      native.PublicFailure event → ∀ owner, graph.actor? event = some owner → owner ∈ excluded)
    (newMembers : ∀ owner ∈ excluded, owner ∈ state.excluded ∨
      ∃ event, graph.actor? event = some owner ∧ native.PublicFailure event) :
    PublicExclusionRecord ⟨native, excluded⟩ := by
  classical
  refine ⟨valid.receipts.step step, fun owner => ⟨?_, ?_⟩⟩
  · intro member
    rcases newMembers owner member with previous | witness
    · obtain ⟨query, acting, failed⟩ := (valid.excluded owner).mp previous
      refine ⟨query, acting, ?_⟩
      exact (step.publicFailure_iff_of_completed failed.completed).mpr failed
    · exact witness
  · rintro ⟨query, acting, failed⟩
    by_cases completed : query ∈ state.native.config.cut.completed
    · apply old
      apply (valid.excluded owner).mpr
      refine ⟨query, acting, ?_⟩
      exact (step.publicFailure_iff_of_completed completed).mp failed
    · exact newEvidence query completed failed owner acting

/-- Initial exclusion is empty and there are no completed failure events. -/
theorem initial (inputs : graph.Inputs) :
    PublicExclusionRecord (⟨State.initial inputs, ∅⟩ : RecoveryState graph) := by
  refine ⟨State.ReceiptsComplete.initial inputs, fun owner => ⟨?_, ?_⟩⟩
  · intro member
    exact (Finset.notMem_empty owner member).elim
  · rintro ⟨event, _, failed⟩
    have completed := failed.completed
    simp [State.initial, EventGraph.Config.initial, EventOrder.Cut.empty] at completed

omit [DecidableEq Player] in
/-- Automatic completion records failures only for owners already excluded. -/
theorem completeAutomatic (valid : PublicExclusionRecord state) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    PublicExclusionRecord (state.completeAutomatic event eligible) := by
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

/-- The full automatic drain preserves exact public exclusion evidence. -/
theorem drainFuel (fuel : Nat) (valid : PublicExclusionRecord state) :
    PublicExclusionRecord (RecoveryState.drainFuel fuel state) := by
  exact RecoveryState.drainFuel_induction PublicExclusionRecord
    (fun _ event eligible previous => previous.completeAutomatic event eligible) fuel state valid

theorem drain (valid : PublicExclusionRecord state) : PublicExclusionRecord state.drain :=
  valid.drainFuel _

/-- Accepted bindings cannot create omission evidence; accepted openings add
exactly the owner whose public resolution failed. -/
theorem inclusionResult (valid : PublicExclusionRecord state) (runtime : EventGraphRuntime graph)
    (message : Message Player (Payload graph)) (native : State graph)
    (accepted : handle runtime state.native message = some native) :
    PublicExclusionRecord (state.inclusionResult message.payload native) := by
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
              · exact Or.inr ⟨actual, acting, Or.inr failed⟩
              · exact Or.inl previous
        · exact Or.inl excluded

omit [DecidableEq Player] in
private theorem expire_publicFailure (runtime : EventGraphRuntime graph)
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
theorem environmentResult (valid : PublicExclusionRecord state) (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime state.native command).support) :
    PublicExclusionRecord (state.environmentResult command native) := by
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
                exact Or.inr ⟨event, acting, expire_publicFailure runtime state.native native
                  valid.receipts event reached changed acting⟩
              · exact Or.inl previous
        · exact Or.inl excluded

theorem submit (valid : PublicExclusionRecord state) (who : Player)
    (submission : WitnessedSubmission graph) :
    PublicExclusionRecord (state.submit who submission) := by
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

theorem handle (valid : PublicExclusionRecord state) (runtime : EventGraphRuntime graph)
    (message : Message Player (WitnessedPacket graph)) (next : RecoveryState graph)
    (accepted : state.handle runtime message = some next) : PublicExclusionRecord next := by
  unfold RecoveryState.handle at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact (valid.inclusionResult runtime _ native rawAccepted).drain
    · cases accepted

theorem environment (valid : PublicExclusionRecord state) (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (next : RecoveryState graph)
    (reached : next ∈ (state.environment runtime command).support) :
    PublicExclusionRecord next := by
  rw [RecoveryState.environment, PMF.support_map] at reached
  obtain ⟨native, realized, rfl⟩ := reached
  exact (valid.environmentResult runtime command native realized).drain

end PublicExclusionRecord

end Vegas.EventGraphRuntime
