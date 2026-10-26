/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.CommitTimingInformationSource
import Vegas.Game.SourcePhaseGame
import Vegas.Game.SequentialRuntimePhases
import Vegas.Game.RecoveryInitialCheckpoint
import Vegas.Game.PhaseExclusionPayoff
import Vegas.Pending.PhaseSingletonTransition
import Interaction.ReactiveRawRoundTrace

/-! # Different commitment partitions have different operational retries

The source closes its two-owner maximal block after Bob's first choice. Alice's
omission then causes a surviving-owner retry, preserving Bob's voided choice.
The singleton runtime archives Alice's failed slot and advances without a retry.
These are actual initialized kernels and legal source traces, not a claim that
no Nash correspondence can preserve an appropriate coarser observation.
-/

noncomputable section

namespace Vegas.Examples.SourcePhasePartition

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open CommitTimingInformation

abbrev sourceEntry : CommitRecoveryState program :=
  .atPoint (ProtocolState.entry program (setup.initialConfig (sourceInitial false))) ∅ 0

def omission : Player → Option (CommitRecoveryMove Player simpleExpr) :=
  fun who => if who = alice then some ⟨.commit alice 1 .bool .failure, true⟩ else none

def bobChoice : Player → Option (CommitRecoveryMove Player simpleExpr) :=
  fun who => if who = bob then some ⟨.commit bob 2 .bool (.success true), false⟩ else none

private def aliceConfig :=
  commitSuccessor 1 (acceptGuard alice 1) (setup.initialConfig (sourceInitial false)) .failure

private def alicePoint : ProtocolState program :=
  .inr (ProtocolState.entry _ aliceConfig)

private def aliceRaw : CommitRecoveryState program :=
  sourceEntry.install (alicePoint, {alice}) (Finset.empty_subset _)

def sourceAfterOmission : CommitRecoveryState program := aliceRaw.close

private theorem omission_not_finished : ¬ aliceRaw.Finished := by
  change ¬ (true = true ∧ 3 = 2)
  decide

private theorem omission_eq : sourceAfterOmission = aliceRaw := by
  unfold sourceAfterOmission CommitRecoveryState.close
  rw [ite_eq_right omission_not_finished]
  exact ite_eq_left rfl

private theorem omission_excluded : sourceAfterOmission.excluded = {alice} := by
  rw [omission_eq]
  rfl

private theorem omission_raw :
    ProtocolState.recoveryStep program sourceEntry.point sourceEntry.excluded omission =
      PMF.pure (alicePoint, {alice}) := by
  simp [ProtocolState.recoveryStep, sourceEntry, omission, program, alice, alicePoint,
    CommitRecoveryState.atPoint, CommitRecoveryMove.missed, OwnAction.binding,
    ProtocolState.entry, aliceConfig]

private theorem step_support {before : CommitRecoveryState program}
    (joint : Player → Option (CommitRecoveryMove Player simpleExpr))
    (point : ProtocolState program) (excluded : Finset Player)
    (monotone : before.excluded ⊆ excluded)
    (raw : ProtocolState.recoveryStep program before.point before.excluded joint =
      PMF.pure (point, excluded)) :
    (before.install (point, excluded) monotone).close ∈ (before.step joint).support := by
  obtain ⟨target, member⟩ := (before.step joint).support_nonempty
  obtain ⟨result, supported, equal⟩ := before.step_raw_result joint target member
  rw [raw, PMF.mem_support_pure_iff] at supported
  have same : result = ⟨(point, excluded), monotone⟩ := Subtype.ext supported
  subst result
  simpa only [equal] using member

theorem source_omission_support : sourceAfterOmission ∈ (sourceEntry.step omission).support :=
  step_support omission alicePoint {alice} (Finset.empty_subset _) omission_raw

private theorem omission_legal : setup.commitRecoveryProtocol.Legal (some sourceEntry)
    omission := by
  refine ⟨fun impossible => impossible, ?_⟩
  intro who
  fin_cases who
  · refine ⟨⟨rfl, by decide⟩, ?_, fun _ => rfl⟩
    exact ⟨.failure, rfl, rfl⟩
  · exact fun active => by cases active.1

private theorem draw_legal : setup.commitRecoveryProtocol.Legal none (fun _ => none) :=
  ⟨fun impossible => impossible, fun _ impossible => impossible⟩

private def sourceDraw : setup.commitRecoveryProtocol.Trace (some sourceEntry) := by
  refine .extend .start (fun _ => none) draw_legal ?_
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨sourceInitial false, (initialLaw_support _).mpr ⟨false, rfl⟩, rfl⟩

def sourceOmissionTrace : setup.commitRecoveryProtocol.Trace (some sourceAfterOmission) :=
  .extend sourceDraw omission omission_legal
    ((PMF.mem_support_map_iff _ _ _).mpr ⟨sourceAfterOmission, source_omission_support, rfl⟩)

private def bobConfig := commitSuccessor 2 (acceptGuard bob 2) aliceConfig (.success true)

private def bobPoint : ProtocolState program := .inr (.inr (ProtocolState.entry _ bobConfig))

private def bobRaw : CommitRecoveryState program :=
  sourceAfterOmission.install (bobPoint, {alice}) (by rw [omission_excluded])

def sourceRetried : CommitRecoveryState program := bobRaw.close

private theorem bob_raw :
    ProtocolState.recoveryStep program sourceAfterOmission.point
      sourceAfterOmission.excluded bobChoice = PMF.pure (bobPoint, {alice}) := by
  rw [omission_eq]
  simp [ProtocolState.recoveryStep, aliceRaw, CommitRecoveryState.install, program, alicePoint,
    ProtocolState.entry, bobChoice, alice, bob, CommitRecoveryMove.missed,
    OwnAction.binding, bobPoint, PMF.pure_map, bobConfig]

private theorem bob_legal : setup.commitRecoveryProtocol.Legal (some sourceAfterOmission)
    bobChoice := by
  rw [omission_eq]
  refine ⟨fun impossible => impossible, ?_⟩
  intro who
  fin_cases who
  · exact fun active => by cases active.1
  · refine ⟨⟨rfl, by decide⟩, ?_, fun bad => Bool.noConfusion bad⟩
    exact ⟨.success true, trivial, rfl⟩

def sourceRetryTrace : setup.commitRecoveryProtocol.Trace (some sourceRetried) :=
  .extend sourceOmissionTrace bobChoice bob_legal
    ((PMF.mem_support_map_iff _ _ _).mpr
      ⟨sourceRetried,
        step_support bobChoice bobPoint {alice} (by rw [omission_excluded]) bob_raw, rfl⟩)

private theorem retried_eq : sourceRetried = bobRaw.retry := by
  apply CommitRecoveryState.close_of_retry
  · dsimp only [CommitRecoveryState.Finished, bobRaw, CommitRecoveryState.install]
    rw [omission_eq]
    exact ⟨rfl, rfl⟩
  · change (({alice} : Finset Player) \ sourceAfterOmission.entryExcluded).Nonempty
    rw [omission_eq]
    exact ⟨alice, by decide⟩
  · change (ProtocolState.commitOwners program sourceAfterOmission.saved \ {alice}).Nonempty
    rw [omission_eq]
    exact ⟨bob, by decide⟩

/-- The source actually returns to its two-owner entry after Bob's first choice. -/
theorem source_retry_generation : sourceRetried.generation = 1 := by
  rw [retried_eq]
  change sourceAfterOmission.generation + 1 = 1
  rw [omission_eq]
  rfl

theorem source_retry_actor : ProtocolState.actor program sourceRetried.point = some alice := by
  rw [retried_eq]
  change ProtocolState.actor program
    (ProtocolState.withHistory program sourceAfterOmission.saved _) = _
  rw [omission_eq]
  rfl

theorem source_retry_bob_recall : ProtocolState.history program sourceRetried.point bob =
    [.commit bob 2 .bool (.success true)] := by
  rw [retried_eq]
  change (ProtocolState.history program bobRaw.restored) bob = _
  rw [CommitRecoveryState.restored, ProtocolState.history_withHistory]
  rw [show bobRaw.point = bobPoint from rfl]
  rfl

abbrev compiled := Vegas.graph setup
abbrev firstEvent : compiled.EventId := ⟨0, by decide⟩
abbrev secondEvent : compiled.EventId := ⟨1, by decide⟩
abbrev physicalRuntime := Vegas.runtime setup
private instance : NeZero compiled.order.eventCount := ⟨by decide⟩
abbrev plan := sequentialRuntimePhasePlan program
abbrev firstPhase := sequentialRuntimePhaseAt program firstEvent
abbrev secondPhase := sequentialRuntimePhaseAt program secondEvent

def physicalInitial : PhaseRuntimeState compiled :=
  PhaseRuntimeState.initial plan (setup.eventInputs (sourceInitial false))

private def nativeInitial : EventGraphRuntime.State compiled :=
  .initial (setup.eventInputs (sourceInitial false))

def clockedNative : EventGraphRuntime.State compiled := { nativeInitial with clock := 1 }

def clocked : PhaseRuntimeState compiled :=
  { physicalInitial with current := ⟨clockedNative, ∅⟩ }

private theorem plan_cons : plan.phases = firstPhase :: secondPhase ::
    [sequentialRuntimePhaseAt program ⟨2, by decide⟩,
      sequentialRuntimePhaseAt program ⟨3, by decide⟩] := by
  simp only [sequentialRuntimePhasePlan]
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
  rfl

private theorem empty_drain (phase : RuntimePhase compiled)
    (state : EventGraphRuntime.State compiled) : phase.drain ⟨state, ∅⟩ = ⟨state, ∅⟩ := by
  apply phase.drain_eq_of_clear
  rintro event ⟨_, automatic⟩
  obtain ⟨owner, _, absent⟩ := automatic.owned
  exact Finset.notMem_empty owner absent

private theorem clocked_normal : clocked.normalize = clocked := by
  have drained := empty_drain firstPhase clockedNative
  change firstPhase.drain clocked.current = clocked.current at drained
  have unfinished : ¬ firstPhase.Finished clocked.current := by
    intro finished
    have done := finished (show firstEvent ∈ firstPhase.events by
      simp only [sequentialRuntimePhaseAt_events, Finset.mem_singleton])
    change firstEvent ∈ (∅ : Finset compiled.EventId) at done
    exact Finset.notMem_empty _ done
  unfold PhaseRuntimeState.normalize
  rw [show clocked.phases = firstPhase :: _ from by
    dsimp only [clocked, physicalInitial]; rw [phaseInitial_eq_raw, plan_cons]]
  rw [PhaseRuntimeState.settle, drained, ite_eq_right unfinished]
  unfold clocked physicalInitial
  rw [phaseInitial_eq_raw, plan_cons]

/-- This clock value is reached by the actual first environment command. -/
theorem singleton_clock_step : physicalInitial.environment physicalRuntime .advanceClock =
    PMF.pure clocked := by
  simp only [PhaseRuntimeState.environment, PhaseRuntimeState.commandAllowed,
    ↓reduceIte, environmentStep, PMF.pure_map]
  have same : ({ physicalInitial with current := (physicalInitial.current.environmentResult
      .advanceClock { physicalInitial.current.native with
        clock := physicalInitial.current.native.clock + 1 }) } : PhaseRuntimeState compiled) =
      clocked := by
    unfold clocked physicalInitial
    rw [phaseInitial_eq_raw]
    rfl
  rw [same, clocked_normal]

private theorem clocked_valid :
    State.Invariant (graph := compiled) (setup.eventInputs (sourceInitial false)) clockedNative :=
  environmentStep_invariant physicalRuntime nativeInitial clockedNative .advanceClock
    (EventGraphRuntime.State.initial_invariant (graph := compiled) _) (by
      change clockedNative ∈ (PMF.pure clockedNative).support
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)

private theorem clocked_ready : clockedNative.config.cut.Ready firstEvent := by decide

private theorem first_unique (event : compiled.EventId)
    (ready : clockedNative.config.cut.Ready event) : event = firstEvent := by
  fin_cases event
  · rfl
  · exact False.elim ((by decide : ¬ clockedNative.config.cut.Ready 1) ready)
  · exact False.elim ((by decide : ¬ clockedNative.config.cut.Ready 2) ready)
  · exact False.elim ((by decide : ¬ clockedNative.config.cut.Ready 3) ready)

def failedNative := clockedNative.completeFailure firstEvent clocked_ready

def failed : RecoveryState compiled :=
  (⟨clockedNative, ∅⟩ : RecoveryState compiled).environmentResult (.expire firstEvent) failedNative

def singletonAfterOmission : PhaseRuntimeState compiled :=
  PhaseRuntimeState.settle plan.phases.tail 0 failed failed
    [⟨⟨0, 0⟩, failedNative⟩]

/-- The actual due expiry archives Alice's singleton and advances without retry. -/
theorem singleton_expiry_step : clocked.environment physicalRuntime (.expire firstEvent) =
    PMF.pure singletonAfterOmission := by
  have actual := PhaseRuntimeState.environment_expire_singleton physicalRuntime firstPhase
    plan.phases.tail 0 (⟨nativeInitial, ∅⟩ : RecoveryState compiled)
    (⟨clockedNative, ∅⟩ : RecoveryState compiled) [] clocked_valid firstEvent
    (sequentialRuntimePhaseAt_events program firstEvent) clocked_ready 0 (by decide)
    (by decide) alice .bool rfl rfl (nodeView_eq_bind rfl rfl)
    (sequentialRuntimePhaseAt_kind_of_binding program firstEvent rfl) (by decide) rfl rfl
    first_unique
  have head : clocked = ⟨firstPhase :: plan.phases.tail, 0,
      ⟨nativeInitial, ∅⟩, ⟨clockedNative, ∅⟩, []⟩ := by
    dsimp only [clocked, physicalInitial]
    rw [phaseInitial_eq_raw, plan_cons]
    rfl
  rw [head]
  exact actual

private theorem failed_excluded : failed.excluded = {alice} := by
  change (if firstEvent ∉ clockedNative.config.cut.completed ∧
    firstEvent ∈ failedNative.config.cut.completed then
      RecoveryState.excludeEvent ∅ firstEvent else ∅) = _
  rw [ite_eq_left (show firstEvent ∉ clockedNative.config.cut.completed ∧
    firstEvent ∈ failedNative.config.cut.completed from by decide)]
  rfl

private theorem singleton_after_eq : singletonAfterOmission =
    ⟨plan.phases.tail, 0, failed, failed, [⟨⟨0, 0⟩, failedNative⟩]⟩ := by
  have drained : secondPhase.drain failed = failed := by
    apply secondPhase.drain_eq_of_clear
    rintro event ⟨inside, eligible⟩
    have same := Finset.mem_singleton.mp
      ((Finset.ext_iff.mp (sequentialRuntimePhaseAt_events program secondEvent) event).mp inside)
    subst event
    have excluded : bob ∈ failed.excluded := eligible.2
    rw [failed_excluded] at excluded
    exact (by decide : bob ∉ ({alice} : Finset Player)) excluded
  have unfinished : ¬ secondPhase.Finished failed := by
    intro finished
    have done := finished (show secondEvent ∈ secondPhase.events by
      simp only [sequentialRuntimePhaseAt_events, Finset.mem_singleton])
    exact (by decide : secondEvent ∉ failedNative.config.cut.completed) done
  unfold singletonAfterOmission
  rw [plan_cons]
  simp only [List.tail_cons]
  rw [PhaseRuntimeState.settle, drained, ite_eq_right unfinished]

/-- Unlike the actual source retry, this actual singleton endpoint keeps generation zero. -/
theorem singleton_generation : singletonAfterOmission.generation = 0 := by
  rw [singleton_after_eq]

theorem singleton_attempt : singletonAfterOmission.attempt = ⟨1, 0⟩ := by
  rw [singleton_after_eq]
  rw [PhaseRuntimeState.attempt, plan_cons]
  rfl

theorem singleton_archive : singletonAfterOmission.retired = [⟨⟨0, 0⟩, failedNative⟩] := by
  rw [singleton_after_eq]

theorem different_retry_generations :
    sourceRetried.generation ≠ singletonAfterOmission.generation := by
  rw [source_retry_generation, singleton_generation]
  decide

def leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket compiled) :=
  fun _ _ => PMF.pure ∅

abbrev app := phaseApplication physicalRuntime leaks

def physicalPrior : PMF app.State :=
  setup.initialLaw.map fun inputs => PhaseRuntimeState.initial plan (setup.eventInputs inputs)

def witnessScheduler : app.Scheduler := fun past _ =>
  PMF.pure (.application (if past.length = 0 then .advanceClock else .expire firstEvent))

def initialExecution : app.Execution := .initial app physicalInitial

def clockedExecution : app.Execution :=
  { initialExecution with
    application := clocked
    environmentRecall := [⟨initialExecution.observeEnvironment app, .application .advanceClock⟩] }

def expiredExecution : app.Execution :=
  { clockedExecution with
    application := singletonAfterOmission
    environmentRecall := clockedExecution.environmentRecall ++
      [⟨clockedExecution.observeEnvironment app, .application (.expire firstEvent)⟩] }

private theorem clock_execution_step :
    initialExecution.environmentStep app (.application .advanceClock) =
      PMF.pure clockedExecution := by
  change ((physicalInitial.environment physicalRuntime .advanceClock).map _).map _ = _
  rw [singleton_clock_step, PMF.pure_map, PMF.pure_map]
  rfl

private theorem expire_execution_step :
    clockedExecution.environmentStep app (.application (.expire firstEvent)) =
      PMF.pure expiredExecution := by
  change ((clocked.environment physicalRuntime (.expire firstEvent)).map _).map _ = _
  rw [singleton_expiry_step, PMF.pure_map, PMF.pure_map]
  rfl

private def initializedTrace :
    (app.protocol physicalPrior 2 witnessScheduler).Trace (some ⟨2, none, initialExecution⟩) := by
  refine .extend .start (fun _ => none) ⟨fun impossible => impossible,
    fun _ impossible => by cases impossible⟩ ?_
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨physicalInitial, ?_, rfl⟩
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨sourceInitial false, (initialLaw_support _).mpr ⟨false, rfl⟩, rfl⟩

/-- Both commands belong to one genuine initialized raw physical trace. No
physical service or equilibrium property is asserted for this short scheduler. -/
theorem singleton_initialized_trace :
    Nonempty ((app.protocol physicalPrior 2 witnessScheduler).Trace
      (some ⟨0, none, expiredExecution⟩)) := by
  obtain ⟨clockTrace⟩ := app.raw_trace_environment physicalPrior 2 witnessScheduler 1
    initialExecution clockedExecution (.application .advanceClock) initializedTrace
    (by exact (PMF.mem_support_pure_iff _ _).mpr rfl)
    (by rw [clock_execution_step]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact app.raw_trace_environment physicalPrior 2 witnessScheduler 0
    clockedExecution expiredExecution (.application (.expire firstEvent)) clockTrace
    (by exact (PMF.mem_support_pure_iff _ _).mpr rfl)
    (by rw [expire_execution_step]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)

/-- The source retry retains an already voided Bob choice; the physical singleton
has advanced to Bob without activating him or recording a Bob response. -/
theorem different_bob_recall :
    (ProtocolState.history program sourceRetried.point bob).length = 1 ∧
      (expiredExecution.recall bob).length = 0 := by
  rw [source_retry_bob_recall]
  exact ⟨rfl, rfl⟩

theorem source_retry_incomplete : setup.protocolReadout (some sourceRetried.point) = none := by
  rw [retried_eq]
  change setup.protocolReadout
    (some (ProtocolState.withHistory program sourceAfterOmission.saved _)) = none
  rw [omission_eq]
  rfl

/-- Immediately after Alice's omission, the source still addresses the entry of
its maximal block; the singleton dispatcher has already installed Bob's slot. -/
theorem source_omission_phase_address :
    (setup.commitRecoveryPublic (some sourceAfterOmission)).2.2 = 0 := by
  rw [omission_eq]
  rfl

theorem different_omission_phase_addresses :
    (setup.commitRecoveryPublic (some sourceAfterOmission)).2.2 ≠
      singletonAfterOmission.attempt.phase := by
  rw [source_omission_phase_address, singleton_attempt]
  decide

/-- The mismatch concerns checkpoints, attempts and recall. Neither displayed
endpoint has completed a typed source readout. -/
theorem singleton_readout_incomplete :
    phaseSourceReadout setup .sequential physicalRuntime leaks
      (some (⟨0, none, expiredExecution⟩ : app.Control)) = none := by
  unfold phaseSourceReadout
  change (if singletonAfterOmission.current.native.config.cut.Terminal then _ else none) = none
  rw [singleton_after_eq]
  exact ite_eq_right (by decide : ¬ failedNative.config.cut.Terminal)

end Vegas.Examples.SourcePhasePartition
