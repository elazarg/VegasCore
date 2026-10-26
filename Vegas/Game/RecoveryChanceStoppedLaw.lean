/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketChanceStoppedLaw
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoverySuccessorBoundary
import Vegas.Game.ServiceChancePhase

/-! # Finite stopped chance phases of the recovery comparison model -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section FiniteChance

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication runtime leaks).Scheduler}
  (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler runtime leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

include initialized nativeLaw completes in
/-- The finite one-packet stopped chance phase has the graph sampling law on
configurations, including the actual first public-exclusion stopping rule. -/
theorem recovery_chance_stopped_configLaw
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (action : (graph setup).Action event)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ((N).runBehavioralUntil certificate players
      (fun stop => LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).map
        (fun final => final.state.map (fun next => next.execution.application.config)) =
      (control.execution.application.config.step event ready action).map some := by
  exact counted_chance_stopped_configLaw (runtime := runtime) (setup := setup) (leaks := leaks)
    (bounds := bounds)
    (completes := Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds
      initialized nativeLaw
    completes) certificate players start current ordered event ready actorless action decoded
    intended

include initialized nativeLaw completes in
/-- The finite chance phase preserves the exact source continuation law. Its
policies and scheduler are the actual comparison policies and recovery scheduler. -/
theorem recovery_chance_stopped_sourceContinuation
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (event : (graph setup).EventId)
    (actorless : (graph setup).actor? event = none)
    (profile : BehavioralProfile setup.program)
    (residual : SourceResidual setup profile rank control.execution.application.config)
    (atRank : event.val = rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ((N).runBehavioralUntil certificate players
      (fun stop => LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).bind
        (fun final => (setup.continuationLaw profile
          (nativeDecodedState setup runtime leaks final.state)).map some) =
      sourceContinuation setup profile rank control.execution.application.config := by
  exact counted_chance_stopped_sourceContinuation (runtime := runtime) (setup := setup) (leaks :=
    leaks) (bounds :=
    bounds) (completes := Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds
      initialized nativeLaw
    completes) certificate players start current event actorless profile residual atRank decoded
    intended

end FiniteChance

end Vegas
