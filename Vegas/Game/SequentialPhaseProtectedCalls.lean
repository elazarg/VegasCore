/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceAsyncTimeliness
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
        (SettlesFreshCalls setup recoveryLeaks owner event bound) state
  | _, .start, _ => trivial
  | _, .extend (source := before) prior joint _ reached, clear => by
      have rawPrior := (nativeMenu).toRawTrace (initialLaw setup) horizon
        (nativeScheduler (recoveryScheduler scheduler)) prior
      have beforeClear := native_clear_before_transition (runtime setup) recoveryLeaks
        (initialLaw setup) (by
          intro native supported
          change native ∈ (setup.initialLaw.map
            (fun draw => State.initial (graph := graph setup) (setup.eventInputs draw))).support
              at supported
          obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨setup.eventInputs draw, rfl⟩) horizon
        (nativeScheduler (recoveryScheduler scheduler)) rawPrior joint reached clear
      have valid := phase_settlesFreshCalls_history horizon scheduler bound inclusion owner event
        owned prior beforeClear
      cases before with
      | none =>
          obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro earlier entry later message split
          simp [ReactiveApplication.Execution.initial] at split
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact settlesFreshCalls_respond setup recoveryLeaks owner event bound execution
                (legalFacts setup recoveryLeaks horizon _ _ rawPrior) who _ valid
          | none =>
              cases remaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have atPrefix := PhaseService.ProtectedInclusion.clear_native_counted setup leaks
                    bounds horizon scheduler bound inclusion prior (beforeClear _ rfl)
                  exact settlesFreshCalls_environment setup recoveryLeaks owner event owned
                    remaining
                    execution atPrefix rawPrior valid command next supported

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
  have valid := phase_settlesFreshCalls_history setup leaks bounds horizon scheduler bound inclusion
    owner event owned prior (by intro current same; cases Option.some.inj same; exact clear)
  have atPrefix := PhaseService.ProtectedInclusion.clear_native_counted setup leaks bounds horizon
    scheduler bound inclusion prior clear
  have rawPrior := (nativeMenu).toRawTrace (initialLaw setup) horizon
    (nativeScheduler (recoveryScheduler scheduler)) prior
  exact settlesFreshCalls_environment setup recoveryLeaks owner event owned remaining execution
    atPrefix rawPrior valid command next reached

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
  have settled := phase_settlesFreshCalls_history setup leaks bounds horizon scheduler bound
    inclusion
    owner event owned trace (by intro current same; cases Option.some.inj same; exact clear)
    earlier entry later message split call sole
  refine ⟨fun late => ?_, settled.1⟩
  by_cases completed : event ∈ control.execution.application.config.cut.completed
  · exact settled.1 completed
  · have atPrefix := PhaseService.ProtectedInclusion.clear_native_counted setup leaks bounds horizon
      scheduler bound inclusion trace clear
    obtain ⟨accepted, receipt⟩ := atPrefix event owner owned earlier later entry message split
      call.emitted call.authored call.addressed call.ready sole completed late
    exact settled.2.1 accepted receipt

end Vegas
