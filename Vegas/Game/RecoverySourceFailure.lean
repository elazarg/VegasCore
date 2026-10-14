/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceFailureRecord
import Vegas.Pending.ExclusionInvariant
import Vegas.Game.OnePacketIntendedProjection

/-! # Permanent exclusions have actual source failure provenance -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {profile : BehavioralProfile setup.program}

private theorem failed_completed {config : (graph setup).Config}
    {event : (graph setup).EventId} (failed : StoreEventFailed config.store event) :
    event ∈ config.cut.completed := by
  obtain ⟨value, read, _⟩ := failed
  change config.outputs event = some value at read
  exact (config.output_available event).mp (by rw [read]; rfl)

private theorem failed_kept {before after : (graph setup).Config}
    (step : ConfigStep setup before after) {event : (graph setup).EventId}
    (completed : event ∈ before.cut.completed) (failed : StoreEventFailed before.store event) :
    event ∈ after.cut.completed ∧ StoreEventFailed after.store event := by
  rcases step with same | ⟨other, ready, action, member⟩
  · subst same
    exact ⟨completed, failed⟩
  · have different : event ≠ other := fun same => ready.1 (same ▸ completed)
    refine ⟨?_, ?_⟩
    · rw [before.step_cut other ready action after member, EventOrder.Cut.mem_complete]
      exact Or.inr completed
    · obtain ⟨value, read, failure⟩ := failed
      refine ⟨value, ?_, failure⟩
      change after.outputs event = _
      obtain ⟨result, same⟩ := step_complete_of_mem member
      rw [same, EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different]
      exact read

private theorem environment_configStep (runtime : EventGraphRuntime (graph setup))
    (before after : EventGraphRuntime.State (graph setup))
    (command : EnvironmentCommand (graph setup))
    (reached : after ∈ (environmentStep runtime before command).support) :
    ConfigStep setup before.config after.config := by
  have ofGraph : GraphStep before after → ConfigStep setup before.config after.config := by
    rintro (⟨same, _, _⟩ | ⟨event, ready, action, member, _, _⟩)
    · exact Or.inl same
    · exact Or.inr ⟨event, ready, action, member⟩
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at reached
      subst after
      exact Or.inl rfl
  | executeSample event => exact ofGraph (graphStep_executeSample runtime _ _ event reached)
  | expire event => exact ofGraph (graphStep_expire runtime _ _ event reached)

private theorem publicationFailed_store {native : EventGraphRuntime.State (graph setup)}
    {event : (graph setup).EventId} (failed : RecoveryState.publicationFailed native event = true) :
    StoreEventFailed native.config.store event := by
  unfold RecoveryState.publicationFailed at failed
  cases view : nodeView (graph setup) event with
  | bind | sample => simp only [view, Bool.false_eq_true] at failed
  | resolve owner payload binding checks outputEq codeEq =>
      rw [view] at failed
      cases result : native.config.outputs event with
      | none => simp only [result, Bool.false_eq_true] at failed
      | some value =>
          rw [result] at failed
          have isFailure : (cast (congrArg EventGraph.EventField.Value outputEq) value :
              PublicationResult (L.Val payload)) = .failure := by
            cases converted : cast (congrArg EventGraph.EventField.Value outputEq) value with
            | failure => rfl
            | success value => simp only [converted, Bool.false_eq_true] at failed
          apply storeEventFailed_of_ref native.config.store event
            (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
              (.publication payload)) rfl (value := .failure)
          · change cast (congrArg Option (congrArg EventGraph.EventField.Value outputEq))
              (native.config.outputs event) = some .failure
            rw [result]
            have castSome {A B : Type} (same : A = B) (value : A) :
                cast (congrArg Option same) (some value) = some (cast same value) := by
              cases same
              rfl
            exact (castSome (congrArg EventGraph.EventField.Value outputEq) value).trans
              (congrArg some isFailure)
          · rfl

private theorem cast_some_inverse {A B : Type} (same : A = B) (value : B) :
    cast (congrArg Option same) (some (cast same.symm value)) = some value := by
  cases same
  rfl

private theorem completeFailure_store (native : EventGraphRuntime.State (graph setup))
    (event : (graph setup).EventId) (ready : native.config.cut.Ready event)
    {owner : Player} (acting : (graph setup).actor? event = some owner) :
    StoreEventFailed (native.completeFailure event ready).config.store event := by
  cases view : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      rw [nodeView_sample_actor outputEq codeEq] at acting
      cases acting
  | bind actor payload outputEq codeEq =>
      apply storeEventFailed_of_ref _ event
        (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
          (.binding actor payload)) rfl (value := .failure)
      · simp only [State.completeFailure, view, State.complete, EventGraph.FieldRef.get?,
          EventGraph.Config.store, EventGraph.Config.complete_output_same]
        exact cast_some_inverse (congrArg EventGraph.EventField.Value outputEq) _
      · rfl
  | resolve actor payload binding checks outputEq codeEq =>
      apply storeEventFailed_of_ref _ event
        (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
          (.publication payload)) rfl (value := .failure)
      · simp only [State.completeFailure, view, State.complete, EventGraph.FieldRef.get?,
          EventGraph.Config.store, EventGraph.Config.complete_output_same]
        exact cast_some_inverse (congrArg EventGraph.EventField.Value outputEq) _
      · rfl

private theorem expire_store_failure (runtime : EventGraphRuntime (graph setup))
    (native next : EventGraphRuntime.State (graph setup)) (event : (graph setup).EventId)
    (reached : next ∈ (environmentStep runtime native (.expire event)).support)
    (changed : next.config ≠ native.config) {owner : Player}
    (acting : (graph setup).actor? event = some owner) :
    StoreEventFailed next.config.store event := by
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
    cases view : nodeView (graph setup) event with
    | sample payload law outputEq codeEq =>
        rw [nodeView_sample_actor outputEq codeEq] at acting
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
  exact completeFailure_store native event ready acting

/-- Exclusion membership has a completed, failed, owned event as a witness, and
all completed failed events carry their decoded source debt. -/
structure RecoveryFailureRecord (profile : BehavioralProfile setup.program)
    (state : RecoveryState (graph setup)) : Prop where
  source : SourceFailureRecord profile state.native.config
  excluded : ∀ owner ∈ state.excluded, ∃ event ∈ state.native.config.cut.completed,
    (graph setup).actor? event = some owner ∧ StoreEventFailed state.native.config.store event

namespace RecoveryFailureRecord

variable {state : RecoveryState (graph setup)}

/-- Native graph progress preserves every previously witnessed exclusion. -/
theorem advance (valid : RecoveryFailureRecord profile state)
    (native : EventGraphRuntime.State (graph setup))
    (step : ConfigStep setup state.native.config native.config) :
    RecoveryFailureRecord profile ⟨native, state.excluded⟩ := by
  refine ⟨valid.source.step step, ?_⟩
  intro owner member
  obtain ⟨event, completed, acting, failed⟩ := valid.excluded owner member
  obtain ⟨completed, failed⟩ := failed_kept step completed failed
  exact ⟨event, completed, acting, failed⟩

/-- A newly excluded owner is justified by its actual failed output. -/
theorem excludeEvent (valid : RecoveryFailureRecord profile state)
    (event : (graph setup).EventId) (failed : StoreEventFailed state.native.config.store event) :
    RecoveryFailureRecord profile
      ⟨state.native, RecoveryState.excludeEvent state.excluded event⟩ := by
  refine ⟨valid.source, ?_⟩
  cases acting : (graph setup).actor? event with
  | none =>
      simpa only [RecoveryState.excludeEvent, acting] using valid.excluded
  | some owner =>
      intro who member
      simp only [RecoveryState.excludeEvent, acting, Finset.mem_insert] at member
      have cases := member
      rcases cases with rfl | previous
      · exact ⟨event, failed_completed failed, acting, failed⟩
      · exact valid.excluded who previous

/-- Automatic service keeps source provenance throughout the full drain. -/
theorem drainFuel (fuel : Nat) (valid : RecoveryFailureRecord profile state) :
    RecoveryFailureRecord profile (RecoveryState.drainFuel fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      unfold RecoveryState.drainFuel
      split
      · rename_i pending
        have stepped := state.completeAutomatic_step (Classical.choose pending)
          (Classical.choose_spec pending)
        obtain ⟨action, member⟩ := stepped
        exact ih (valid.advance _ (Or.inr ⟨_, _, action, member⟩))
      · exact valid

theorem drain (valid : RecoveryFailureRecord profile state) :
    RecoveryFailureRecord profile state.drain := valid.drainFuel _

/-- The raw inclusion classifier is justified before automatic completion. -/
theorem inclusionResult (valid : RecoveryFailureRecord profile state)
    (runtime : EventGraphRuntime (graph setup)) (message : Message Player (Payload (graph setup)))
    (native : EventGraphRuntime.State (graph setup))
    (accepted : handle runtime state.native message = some native) :
    RecoveryFailureRecord profile (state.inclusionResult message.payload native) := by
  obtain ⟨event, _, ready, action, member⟩ :=
    handle_config_mem_step runtime state.native native message accepted
  have next := valid.advance native (Or.inr ⟨event, ready, action, member⟩)
  cases packet : message.payload with
  | commitment => exact next
  | malformed => exact next
  | opening event candidate raw =>
      change RecoveryFailureRecord profile
        ⟨native, if RecoveryState.publicationFailed native event then
          RecoveryState.excludeEvent state.excluded event else state.excluded⟩
      split
      · rename_i failed
        exact next.excludeEvent event (publicationFailed_store failed)
      · exact next

/-- The raw environment classifier is justified before automatic completion. -/
theorem environmentResult (valid : RecoveryFailureRecord profile state)
    (runtime : EventGraphRuntime (graph setup)) (command : EnvironmentCommand (graph setup))
    (native : EventGraphRuntime.State (graph setup))
    (reached : native ∈ (environmentStep runtime state.native command).support) :
    RecoveryFailureRecord profile (state.environmentResult command native) := by
  have next := valid.advance native
    (environment_configStep runtime state.native native command reached)
  cases command with
  | advanceClock => exact next
  | executeSample => exact next
  | expire event =>
      change RecoveryFailureRecord profile
        ⟨native, if event ∉ state.native.config.cut.completed ∧
          event ∈ native.config.cut.completed then
            RecoveryState.excludeEvent state.excluded event else state.excluded⟩
      split
      · rename_i completed
        have changed : native.config ≠ state.native.config := by
          intro same
          rw [same] at completed
          exact completed.1 completed.2
        cases acting : (graph setup).actor? event with
        | none => simpa only [RecoveryState.excludeEvent, acting] using next
        | some owner =>
            exact next.excludeEvent event
              (expire_store_failure runtime state.native native event reached changed acting)
      · exact next

theorem submit (valid : RecoveryFailureRecord profile state) (who : Player)
    (submission : WitnessedSubmission (graph setup)) :
    RecoveryFailureRecord profile (state.submit who submission) := by
  apply valid.advance _ (Or.inl ?_)
  change (submitStep _ who _).config = _
  rw [submitStep_config, (submission.call.register_facts who state.native).1]

theorem handle (valid : RecoveryFailureRecord profile state)
    (runtime : EventGraphRuntime (graph setup))
    (message : Message Player (WitnessedPacket (graph setup))) (next : RecoveryState (graph setup))
    (accepted : state.handle runtime message = some next) : RecoveryFailureRecord profile next := by
  unfold RecoveryState.handle at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact (valid.inclusionResult runtime _ native rawAccepted).drain
    · cases accepted

theorem environment (valid : RecoveryFailureRecord profile state)
    (runtime : EventGraphRuntime (graph setup)) (command : EnvironmentCommand (graph setup))
    (next : RecoveryState (graph setup))
    (reached : next ∈ (state.environment runtime command).support) :
    RecoveryFailureRecord profile next := by
  rw [RecoveryState.environment, PMF.support_map] at reached
  obtain ⟨native, realized, rfl⟩ := reached
  exact (valid.environmentResult runtime command native realized).drain

/-- Every permanent exclusion is source debt at the actual decoded prefix. -/
theorem owesFailure (valid : RecoveryFailureRecord profile state) {rank : Nat}
    (ordered : state.native.config.cut.IsPrefix rank) {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank state.native.config = some point)
    {owner : Player} (member : owner ∈ state.excluded) :
    ProtocolState.OwesFailure owner setup.program point := by
  obtain ⟨event, completed, acting, failed⟩ := valid.excluded owner member
  exact valid.source.owesFailure ordered decoded completed acting failed

/-- The public permanent-exclusion classifier implies source debt at the
configuration's actual decoded point. -/
theorem owesFailure_of_decodedPoint (valid : RecoveryFailureRecord profile state)
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup state.native.config = some point)
    {owner : Player} (member : owner ∈ state.excluded) :
    ProtocolState.OwesFailure owner setup.program point := by
  obtain ⟨rank, ⟨residual⟩, _⟩ := valid.source
  rw [decodedPoint_eq residual] at decoded
  have same := Option.some.inj decoded
  rw [← same]
  exact valid.owesFailure residual.checkpoint.ordered residual.decode member

end RecoveryFailureRecord

/-- Actual recovery histories retain source failure provenance through arbitrary
responses, packet handling, scheduler commands, and automatic completion. -/
theorem recoveryFailureRecord_history
    (profile : BehavioralProfile setup.program)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    (control : (recoveryApplication (runtime setup) leaks).Control)
    (trace : ((recoveryApplication (runtime setup) leaks).protocol
      ((initialLaw setup).map fun native => (⟨native, ∅⟩ : RecoveryState (graph setup)))
      horizon scheduler).Trace (some control)) :
    RecoveryFailureRecord profile control.execution.application := by
  let app := recoveryApplication (runtime setup) leaks
  have preserved : app.Invariant (RecoveryFailureRecord profile) :=
    ⟨fun _ who material valid => valid.submit who material,
      fun _ message next valid accepted => valid.handle _ message next accepted,
      fun _ command next valid realized => valid.environment _ command next realized⟩
  apply preserved.history _ horizon scheduler ?_ trace
  intro state supported
  rw [PMF.support_map] at supported
  obtain ⟨native, supported, rfl⟩ := supported
  rw [initialLaw, serviceInitialLaw, PMF.support_map] at supported
  obtain ⟨initial, _, rfl⟩ := supported
  refine ⟨SourceFailureRecord.initial setup profile initial, ?_⟩
  intro owner member
  exact (Finset.notMem_empty owner member).elim

end Vegas
