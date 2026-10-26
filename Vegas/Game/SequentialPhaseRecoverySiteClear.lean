/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComponents
import Vegas.Game.PhaseRecoveryInformation

/-! # Clear physical states throughout projected decision fibers -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "P" => phaseApplication runtime leaks
local notation "A" => recoveryApplication runtime (recoveryLeaks setup leaks)
local notation "M" => model setup runtime leaks bounds horizon scheduler
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "rawModel" => ReactiveApplication.information (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "RecoveryProtocol" => ReactiveApplication.ResponseMenu.protocol (RecoveryMenu)
    (RecoveryPrior)
  horizon (RecoveryScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState runtime leaks
    RecoveryLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information runtime leaks
    RecoveryLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "RecoveryClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- Every history in a projected genuine clear phase decision fiber is a
controlled clear recovery history, including histories of zero belief mass. -/
theorem recovery_informationHistory_controlled_of_projected_clear
    (who : Player) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (clear : view.application.2.excluded = ∅)
    (site : (R).InformationSite who)
    (input : site.1 = projectInfo (some (past, view)))
    (history : (R).InformationHistory who site.1) :
    ∃ current : (A).Control,
      history.1.state = some current ∧ current.execution.application.excluded = ∅ := by
  have active := InformationSite.active (R) site history
  obtain ⟨current, state, acting⟩ := (A).control_of_active (RecoveryPrior) horizon
      (RecoveryScheduler)
    ((RecoveryMenu).toRawHistory (RecoveryPrior) horizon (RecoveryScheduler) history.1) who active
  change history.1.state = some current at state
  have observed := ((RecoveryMenu).info (RecoveryPrior) horizon (RecoveryScheduler) who
    history.1.trace).symm.trans (history.2.trans input)
  rw [state] at observed
  simp only [ReactiveApplication.observe, acting, ↓reduceIte, PhaseRecoveryProjection.information,
    Option.map_some] at observed
  have flags := congrArg (fun pair => pair.2.application.2) (Option.some.inj observed)
  exact ⟨current, state, flags.trans clear⟩

end Vegas.SequentialPhase
