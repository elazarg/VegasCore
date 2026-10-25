/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseRecoveryStep
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison

/-! # Exact original recovery law stopped at exclusion or a physical guard

The complete projected physical execution is retained at the stopping endpoint,
including all traffic, receipts and own scheduler/player records. Only clear
source callbacks are decoded. No arbitrary old-history lifting, service contract
transfer or equivalence of post-exclusion archive observations is assumed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))
  (included : menu.IncludedIn (PhaseCount.onePacketMenu runtime leaks bounds))
  (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "plan" => sequentialRuntimePhasePlan program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "phaseInitial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "recoveryInitial" =>
  inputs.map (fun input => RecoveryState.mk (State.initial input) ∅)
local notation "recoveryScheduler" =>
  SequentialPhaseSchedulerInformation.scheduler program runtime leaks recoveryLeaks scheduler
local notation "M" =>
  ReactiveApplication.ResponseMenu.information (menu) phaseInitial horizon scheduler
local notation "N" =>
  ReactiveApplication.information (R) recoveryInitial horizon recoveryScheduler
local notation "projection" => PhaseRecoveryProjection.protocolState runtime leaks recoveryLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "recoveryClear" => ReactiveApplication.stateInvariant (app := R)
  (fun state => RecoveryState.excluded state = ∅)

include included in
/-- Arbitrary counted phase policies and their old own-information decodings
have identical physical laws stopped at exclusion or any current-state guard,
from every pair of matched actual histories.
The first-exclusion successor is retained rather than collapsed to a failure atom. -/
theorem run_until_exclusion_or_guard_map_state
    (phaseCertificate : ((menu).protocol phaseInitial horizon scheduler).WellFoundedHistories)
    (recoveryCertificate :
      ((R).protocol recoveryInitial horizon recoveryScheduler).WellFoundedHistories)
    (guard : (R).ProtocolState → Prop)
    (profile : ∀ who, (M).BehavioralPolicy who)
    (first : ((menu).protocol phaseInitial horizon scheduler).History)
    (second : ((R).protocol recoveryInitial horizon recoveryScheduler).History)
    (same : projection first.state = second.state) :
    ((M).runBehavioralUntil phaseCertificate profile
      (fun history => ¬ phaseClear history.state ∨ guard (projection history.state)) first).map
        (fun history => projection history.state) =
      ((N).runBehavioralUntil recoveryCertificate
        (fun who => behavioralPolicy program runtime leaks menu inputs horizon scheduler who
          (profile who)) (fun history => ¬ recoveryClear history.state ∨ guard history.state)
        second).map
          History.state := by
  classical
  apply (M).runBehavioralUntil_map_eq_of_step_maps (N) phaseCertificate recoveryCertificate
    profile (fun who => behavioralPolicy program runtime leaks menu inputs horizon scheduler who
      (profile who))
    (fun history => ¬ phaseClear history.state ∨ guard (projection history.state))
    (fun history => ¬ recoveryClear history.state ∨ guard history.state)
    (fun history => projection history.state)
    History.state ?_ ?_ first second same
  · intro first second matched
    change ((¬ phaseClear first.state ∨ guard (projection first.state)) ∨
        (P).terminal first.state) ↔
      ((¬ recoveryClear second.state ∨ guard second.state) ∨ (R).terminal second.state)
    rw [← matched]
    cases first.state <;> rfl
  · intro first second matched going _running
    exact run_one_map_state_history program runtime leaks menu bounds included inputs
      horizon scheduler profile
      first second matched (not_not.mp (not_or.mp going).1)

include included in
/-- Starting from the real input law, play stopped at exclusion or a physical guard has the
same complete physical state law under every counted phase profile and deviation. -/
theorem run_until_exclusion_or_guard_initial_map_state
    (guard : (R).ProtocolState → Prop)
    (profile : ∀ who, (M).BehavioralPolicy who) :
    ((M).runBehavioralUntil
      ((menu).bounded phaseInitial horizon scheduler).wellFoundedHistories profile
      (fun history => ¬ phaseClear history.state ∨ guard (projection history.state))
      ((menu).protocol phaseInitial horizon scheduler).initHistory).map
        (fun history => projection history.state) =
      ((N).runBehavioralUntil
        ((R).bounded recoveryInitial horizon recoveryScheduler).wellFoundedHistories
        (fun who => behavioralPolicy program runtime leaks menu inputs horizon scheduler who
          (profile who)) (fun history => ¬ recoveryClear history.state ∨ guard history.state)
        ((R).protocol recoveryInitial horizon recoveryScheduler).initHistory).map
          History.state :=
  run_until_exclusion_or_guard_map_state program runtime leaks menu bounds included inputs
    horizon scheduler
    _ _ guard profile
    _ _ rfl

end Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy
