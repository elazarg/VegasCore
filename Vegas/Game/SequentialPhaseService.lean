/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseClearLift
import Vegas.Pending.PhaseClearService

/-! # Native service at actual clear recovery counted prefixes

Reverse counted trace lifting instantiates the physical phase contracts at an
actual phase prefix for every recovery counterfactual. The conclusions
are fixed-execution native predicates, not unrestricted raw service contracts.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan

/-- Forgetting permanent exclusion after phase erasure is the original native projection. -/
theorem native_execution (current : (phaseApplication runtime leaks).Execution) :
    RecoveryProjection.execution runtime recoveryLeaks
        (execution runtime leaks recoveryLeaks current) =
      PhaseNativeProjection.execution runtime leaks plan current := by
  have player : (RecoveryProjection.playerEntry runtime recoveryLeaks) ∘
        (playerEntry runtime leaks recoveryLeaks) =
      PhaseNativeProjection.playerEntry runtime leaks plan := rfl
  have environment : (RecoveryProjection.environmentEntry runtime recoveryLeaks) ∘
        (environmentEntry runtime leaks recoveryLeaks) =
      PhaseNativeProjection.environmentEntry runtime leaks plan := by
    funext entry
    cases entry with
    | mk view operation => cases operation <;> rfl
  simp only [RecoveryProjection.execution, execution, PhaseNativeProjection.execution,
    List.map_map, player, environment]

end PhaseRecoveryProjection

namespace PhaseService

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (Vegas.graph setup)))
  (bounds : MessageBounds (Vegas.graph setup))

local notation "inputs" => PMF.map setup.eventInputs setup.initialLaw
local notation "plan" => sequentialRuntimePhasePlan setup.program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "canonical" => ReactiveApplication.SubmissionNormalization.menu
  (PhaseCount.normalization runtime leaks)
  (PhaseCount.onePacketMenu runtime leaks bounds)
local notation "included" => PhaseCount.normalized_onePacket_included runtime
  leaks bounds
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan) (inputs)
local notation "recoveryInitial" => PMF.map (fun native => RecoveryState.mk native ∅)
  (initialLaw setup)
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime recoveryLeaks bounds
local notation "recoveryScheduler" => SequentialPhaseSchedulerInformation.scheduler setup.program
  runtime leaks recoveryLeaks

private theorem exists_phase_control_of_clear_recovery
    (horizon : Nat) (scheduler : (P).Scheduler) {current : (R).Control}
    (trace : ((RecoveryMenu).protocol recoveryInitial horizon (recoveryScheduler scheduler)).Trace
      (some current)) (clear : current.execution.application.excluded = ∅) :
    ∃ phase : (P).Control, ∃ _trace :
      ((PhaseCount.onePacketMenu runtime leaks bounds).protocol phaseInitial horizon
        scheduler).Trace (some phase),
      PhaseRecoveryProjection.control runtime leaks recoveryLeaks phase =
        current := by
  obtain ⟨phase, endpoint, _length⟩ := exists_canonical_phase_of_clear_recovery_trace setup
    runtime leaks
    bounds horizon scheduler trace clear
  cases phaseAt : phase.state with
  | none =>
      rw [phaseAt] at endpoint
      cases endpoint
  | some phaseControl =>
      have actual := (included).trace phaseInitial horizon scheduler phase.trace
      rw [phaseAt] at actual endpoint
      exact ⟨phaseControl, actual, Option.some.inj endpoint⟩

/-- Phase opportunity supplies the native fixed-execution condition at every
actual clear recovery counted prefix, including counterfactual ones. -/
theorem Opportunity.clear_recovery_onePacket
    (horizon : Nat) (scheduler : (P).Scheduler) (delay : (Vegas.graph setup).EventId → Nat)
    (opportunity : Opportunity runtime leaks phaseInitial horizon scheduler delay)
    {current : (R).Control}
    (trace : ((RecoveryMenu).protocol recoveryInitial horizon (recoveryScheduler scheduler)).Trace
      (some current)) (clear : current.execution.application.excluded = ∅) :
    Vegas.EventGraphRuntime.OpportunityAt runtime recoveryLeaks
      (RecoveryProjection.execution runtime recoveryLeaks current.execution)
        delay := by
  obtain ⟨phase, counted, endpoint⟩ := exists_phase_control_of_clear_recovery setup runtime leaks
    bounds
    horizon scheduler trace clear
  have actual := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    phaseInitial horizon scheduler counted
  have native := OpportunityAt.nativeProjection runtime leaks plan phase.execution
    delay (opportunity phase actual)
  rw [← endpoint]
  change Vegas.EventGraphRuntime.OpportunityAt runtime recoveryLeaks
    (RecoveryProjection.execution runtime recoveryLeaks
      (PhaseRecoveryProjection.execution runtime leaks recoveryLeaks phase.execution))
        delay
  rw [PhaseRecoveryProjection.native_execution]
  exact native

/-- Physical sole-packet protection supplies the exact native predicate at every
actual clear recovery counted prefix; no author visibility rule is imposed. -/
theorem ProtectedInclusion.clear_recovery_onePacket
    (horizon : Nat) (scheduler : (P).Scheduler) (bound : (Vegas.graph setup).EventId → Nat)
    (inclusion : ProtectedInclusion runtime leaks phaseInitial horizon scheduler
      bound)
    {current : (R).Control}
    (trace : ((RecoveryMenu).protocol recoveryInitial horizon (recoveryScheduler scheduler)).Trace
      (some current)) (clear : current.execution.application.excluded = ∅) :
    Vegas.EventGraphRuntime.ProtectedInclusionAt runtime recoveryLeaks
      (RecoveryProjection.execution runtime recoveryLeaks current.execution)
        bound := by
  obtain ⟨phase, counted, endpoint⟩ := exists_phase_control_of_clear_recovery setup runtime leaks
    bounds
    horizon scheduler trace clear
  have phaseClear : phase.execution.application.current.excluded = ∅ := by
    rw [← endpoint] at clear
    exact clear
  have native := ProtectedInclusion.clear_native_onePacket runtime leaks plan bounds
    inputs horizon scheduler bound inclusion (sequentialRuntimePhasePlan_singleton setup.program)
    counted phaseClear
  rw [← endpoint]
  change Vegas.EventGraphRuntime.ProtectedInclusionAt runtime recoveryLeaks
    (RecoveryProjection.execution runtime recoveryLeaks
      (PhaseRecoveryProjection.execution runtime leaks recoveryLeaks phase.execution))
        bound
  rw [PhaseRecoveryProjection.native_execution]
  exact native

/-- Actual terminal recovery counted prefixes finish the semantic graph,
including terminality caused by exhaustion of the physical scheduler horizon. -/
theorem CompletesPlay.clear_recovery_onePacket
    (horizon : Nat) (scheduler : (P).Scheduler)
    (completes : CompletesPlay runtime leaks phaseInitial horizon scheduler)
    {current : (R).Control}
    (trace : ((RecoveryMenu).protocol recoveryInitial horizon (recoveryScheduler scheduler)).Trace
      (some current)) (clear : current.execution.application.excluded = ∅)
    (terminal : (R).terminal (some current)) :
    current.execution.application.native.config.cut.Terminal := by
  obtain ⟨phase, counted, endpoint⟩ := exists_phase_control_of_clear_recovery setup runtime leaks
    bounds
    horizon scheduler trace clear
  have actual := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    phaseInitial horizon scheduler counted
  rw [← endpoint] at terminal ⊢
  exact completes phase actual terminal

end PhaseService
end Vegas.EventGraphRuntime
