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
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)

local notation "P" => phaseApplication (runtime setup) leaks
local notation "A" => recoveryApplication (runtime setup) (recoveryLeaks setup leaks)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "rawModel" => ReactiveApplication.information (A) (oldInitial) horizon (oldScheduler)
local notation "oldProtocol" => ReactiveApplication.ResponseMenu.protocol (oldMenu) (oldInitial)
  horizon (oldScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (oldInitial) horizon (oldScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks oldLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks oldLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "oldClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

/-- Every history in a projected genuine clear phase decision fiber is a
controlled clear original recovery history, including histories of zero belief mass. -/
theorem recovery_informationHistory_controlled_of_projected_clear
    (who : Player) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (clear : view.application.2.excluded = ∅)
    (site : (R).InformationSite who)
    (input : site.1 = projectInfo (some (past, view)))
    (history : (R).InformationHistory who site.1) :
    ∃ current : (A).Control,
      history.1.state = some current ∧ current.execution.application.excluded = ∅ := by
  have active := InformationSite.active (R) site history
  obtain ⟨current, state, acting⟩ := (A).control_of_active (oldInitial) horizon (oldScheduler)
    ((oldMenu).toRawHistory (oldInitial) horizon (oldScheduler) history.1) who active
  change history.1.state = some current at state
  have observed := ((oldMenu).info (oldInitial) horizon (oldScheduler) who
    history.1.trace).symm.trans (history.2.trans input)
  rw [state] at observed
  simp only [ReactiveApplication.observe, acting, ↓reduceIte, PhaseRecoveryProjection.information,
    Option.map_some] at observed
  have flags := congrArg (fun pair => pair.2.application.2) (Option.some.inj observed)
  exact ⟨current, state, flags.trans clear⟩

end Vegas.SequentialPhase
