/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseService

/-! # Native counted source service derived from physical singleton phase service

Every actual native counted prefix with clear public evidence has a genuine
recovery counted lift. The phase service therefore supplies its native timing
and terminal-completion predicates at all such source counterfactuals.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (Vegas.graph setup)))
  (bounds : MessageBounds (Vegas.graph setup))

local notation "inputs" => PMF.map setup.eventInputs setup.initialLaw
local notation "plan" => sequentialRuntimePhasePlan setup.program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication (Vegas.runtime setup) leaks
local notation "R" => recoveryApplication (Vegas.runtime setup) recoveryLeaks
local notation "N" => application setup recoveryLeaks
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan) (inputs)
local notation "recoveryInitial" => PMF.map (fun native => RecoveryState.mk native ∅)
  (initialLaw setup)
local notation "old" => Recovery.onePacketMenu (Vegas.runtime setup) recoveryLeaks bounds
local notation "nativeMenu" => MessageBounds.onePacketMenu (Vegas.runtime setup)
  recoveryLeaks bounds
local notation "recoveryScheduler" => SequentialPhaseSchedulerInformation.scheduler setup.program
  (Vegas.runtime setup) leaks recoveryLeaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (Vegas.runtime setup)
  recoveryLeaks

private theorem exists_recovery_of_clear_native_onePacket
    (horizon : Nat) (scheduler : (P).Scheduler) {current : (N).Control}
    (trace : (onePacketProtocol setup recoveryLeaks bounds horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace (some current))
    (clear : ExclusionEvidence 0 ∅
      (⟨current.execution.application, ∅⟩ : RecoveryState (Vegas.graph setup))) :
    Nonempty (((old).protocol recoveryInitial horizon (recoveryScheduler scheduler)).Trace
      (some (RecoveryProjection.liftControl (Vegas.runtime setup) recoveryLeaks current))) := by
  have initialized : ∀ value ∈ (recoveryInitial).support, ∃ draw,
      value = (⟨State.initial draw, ∅⟩ : RecoveryState (Vegas.graph setup)) := by
    intro value supported
    obtain ⟨native, nativeSupported, rfl⟩ := PMF.support_map .. ▸ supported
    change native ∈ (setup.initialLaw.map
      (fun draw => State.initial (graph := Vegas.graph setup) (setup.eventInputs draw))).support
        at nativeSupported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ nativeSupported
    exact ⟨setup.eventInputs draw, rfl⟩
  have nativeLaw : (recoveryInitial).map RecoveryState.native = initialLaw setup := by
    simp only [PMF.map_comp, Function.comp_def]
    exact PMF.map_id _
  have nativeTrace : ((nativeMenu).protocol ((recoveryInitial).map RecoveryState.native) horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace (some current) := by
    rw [nativeLaw]
    exact trace
  let native : ((nativeMenu).protocol ((recoveryInitial).map RecoveryState.native) horizon
      (nativeScheduler (recoveryScheduler scheduler))).History := ⟨some current, nativeTrace⟩
  have publicClear : ∀ found, native.state = some found →
      ExclusionEvidence 0 ∅
        (⟨found.execution.application, ∅⟩ : RecoveryState (Vegas.graph setup)) := by
    intro found same
    cases Option.some.inj same
    exact clear
  obtain ⟨recovered, rawEq⟩ := RecoveryProjection.exists_recoveryBoundedHistory
    (Vegas.runtime setup) recoveryLeaks bounds recoveryInitial initialized horizon
      (recoveryScheduler scheduler) native publicClear
  have endpoint := congrArg (fun history : ((R).protocol recoveryInitial horizon
      (recoveryScheduler scheduler)).History => history.state) rawEq
  change recovered.state =
    some (RecoveryProjection.liftControl (Vegas.runtime setup) recoveryLeaks current) at endpoint
  exact ⟨endpoint ▸ recovered.trace⟩

/-- Physical phase opportunity holds pointwise at every actual public-clear
native source counted prefix under the derived native scheduler. -/
theorem Opportunity.clear_native_counted
    (horizon : Nat) (scheduler : (P).Scheduler) (delay : (Vegas.graph setup).EventId → Nat)
    (opportunity : Opportunity (Vegas.runtime setup) leaks phaseInitial horizon scheduler delay)
    {current : (N).Control}
    (trace : (onePacketProtocol setup recoveryLeaks bounds horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace (some current))
    (clear : ExclusionEvidence 0 ∅
      (⟨current.execution.application, ∅⟩ : RecoveryState (Vegas.graph setup))) :
    Vegas.EventGraphRuntime.OpportunityAt (Vegas.runtime setup) recoveryLeaks current.execution
      delay := by
  obtain ⟨lifted⟩ := exists_recovery_of_clear_native_onePacket setup leaks bounds horizon scheduler
    trace clear
  have actual := Opportunity.clear_recovery_onePacket setup leaks bounds horizon scheduler delay
    opportunity lifted rfl
  change Vegas.EventGraphRuntime.OpportunityAt (Vegas.runtime setup) recoveryLeaks
    (RecoveryProjection.execution (Vegas.runtime setup) recoveryLeaks
      (RecoveryProjection.liftExecution (Vegas.runtime setup) recoveryLeaks current.execution))
        delay at actual
  simpa only [RecoveryProjection.execution_liftExecution] using actual

/-- Physical sole-packet protection supplies the native fixed-execution condition
at every actual public-clear counted source prefix, for every retained owner packet. -/
theorem ProtectedInclusion.clear_native_counted
    (horizon : Nat) (scheduler : (P).Scheduler) (bound : (Vegas.graph setup).EventId → Nat)
    (inclusion : ProtectedInclusion (Vegas.runtime setup) leaks phaseInitial horizon scheduler
      bound)
    {current : (N).Control}
    (trace : (onePacketProtocol setup recoveryLeaks bounds horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace (some current))
    (clear : ExclusionEvidence 0 ∅
      (⟨current.execution.application, ∅⟩ : RecoveryState (Vegas.graph setup))) :
    Vegas.EventGraphRuntime.ProtectedInclusionAt (Vegas.runtime setup) recoveryLeaks
      current.execution bound := by
  obtain ⟨lifted⟩ := exists_recovery_of_clear_native_onePacket setup leaks bounds horizon scheduler
    trace clear
  have actual := ProtectedInclusion.clear_recovery_onePacket setup leaks bounds horizon scheduler
    bound inclusion lifted rfl
  change Vegas.EventGraphRuntime.ProtectedInclusionAt (Vegas.runtime setup) recoveryLeaks
    (RecoveryProjection.execution (Vegas.runtime setup) recoveryLeaks
      (RecoveryProjection.liftExecution (Vegas.runtime setup) recoveryLeaks current.execution))
        bound at actual
  simpa only [RecoveryProjection.execution_liftExecution] using actual

/-- Actual native terminal counted prefixes complete the graph under physical
phase completion, including endpoints reached by physical horizon exhaustion. -/
theorem CompletesPlay.clear_native_counted
    (horizon : Nat) (scheduler : (P).Scheduler)
    (completes : CompletesPlay (Vegas.runtime setup) leaks phaseInitial horizon scheduler)
    {current : (N).Control}
    (trace : (onePacketProtocol setup recoveryLeaks bounds horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace (some current))
    (clear : ExclusionEvidence 0 ∅
      (⟨current.execution.application, ∅⟩ : RecoveryState (Vegas.graph setup)))
    (terminal : (N).terminal (some current)) :
    current.execution.application.config.cut.Terminal := by
  obtain ⟨lifted⟩ := exists_recovery_of_clear_native_onePacket setup leaks bounds horizon scheduler
    trace clear
  exact CompletesPlay.clear_recovery_onePacket setup leaks bounds horizon scheduler completes
    lifted rfl terminal

end Vegas.EventGraphRuntime.PhaseService
