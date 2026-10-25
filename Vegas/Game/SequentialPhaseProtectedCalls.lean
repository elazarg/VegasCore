/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCountedService
import Vegas.Game.SequentialPhaseNativeService

/-! # Protected native counted calls under physical singleton phase service

Every clear counted predecessor supplies the original native sole-packet
inclusion predicate. Existing response and environment settlement kernels then
settle actual fresh calls, including an environment move causing the first failure.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

local notation "inputs" => PMF.map setup.eventInputs setup.initialLaw
local notation "plan" => sequentialRuntimePhasePlan setup.program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication (runtime setup) leaks
local notation "N" => application setup recoveryLeaks
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan) (inputs)
local notation "nativeMenu" => MessageBounds.onePacketMenu (runtime setup) recoveryLeaks bounds
local notation "recoveryScheduler" => SequentialPhaseSchedulerInformation.scheduler setup.program
  (runtime setup) leaks recoveryLeaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) recoveryLeaks

/-- Every fresh call settles at every actual clear native counted history under
physical phase inclusion. Service is instantiated only at genuine counted prefixes. -/
theorem phase_settlesFreshCalls_history
    (horizon : Nat) (scheduler : (P).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks phaseInitial horizon
      scheduler bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    ∀ {state}
      (_trace : (onePacketProtocol setup recoveryLeaks bounds horizon
        (nativeScheduler (recoveryScheduler scheduler))).Trace state),
      (∀ current, state = some current → ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) →
      ReactiveApplication.serviceInvariant
        (SettlesFreshCalls setup recoveryLeaks owner event bound) state := by
  exact settlesFreshCalls_counted_clear_history setup recoveryLeaks bounds horizon
    (nativeScheduler (recoveryScheduler scheduler)) bound
    (fun control prior clear => PhaseService.ProtectedInclusion.clear_native_counted setup leaks
      bounds horizon scheduler bound inclusion prior clear) owner event owned

/-- One command from an actual clear counted prefix preserves settlement even
when this command creates the first public failure; no service is imposed after it. -/
theorem phase_settlesFreshCalls_environment
    (horizon : Nat) (scheduler : (P).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks phaseInitial horizon
      scheduler bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (remaining : Nat) (execution : (N).Execution)
    (prior : (onePacketProtocol setup recoveryLeaks bounds horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (command : (N).Command) (next : (N).Execution)
    (reached : next ∈ (execution.environmentStep (N) command).support) :
    SettlesFreshCalls setup recoveryLeaks owner event bound next := by
  exact settlesFreshCalls_counted_clear_environment setup recoveryLeaks bounds horizon
    (nativeScheduler (recoveryScheduler scheduler)) bound
    (fun control earlier clear => PhaseService.ProtectedInclusion.clear_native_counted setup leaks
      bounds horizon scheduler bound inclusion earlier clear) owner event owned remaining execution
    prior clear command next reached

/-- Actual clear counted prefixes carry accepting receipts for every completed
protected fresh call, and once its original strict protected window has elapsed. -/
theorem phase_prescribed_packet_settles
    (horizon : Nat) (scheduler : (P).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks phaseInitial horizon
      scheduler bound)
    (control : (N).Control)
    (trace : (onePacketProtocol setup recoveryLeaks bounds horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace (some control))
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (earlier later : List (N).PlayerEntry) (entry : (N).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup recoveryLeaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) recoveryLeaks other event message.id) :
    (entry.beforeView.application.publicView.clock + bound event <
        control.execution.application.clock → (message.id, true) ∈ control.execution.receipts) ∧
      (event ∈ control.execution.application.config.cut.completed →
        (message.id, true) ∈ control.execution.receipts) := by
  exact prescribed_packet_counted_clear_settles setup recoveryLeaks bounds horizon
    (nativeScheduler (recoveryScheduler scheduler)) bound
    (fun control prior clear => PhaseService.ProtectedInclusion.clear_native_counted setup leaks
      bounds horizon scheduler bound inclusion prior clear) control trace clear event owner owned
    earlier later entry message split call sole

end Vegas
