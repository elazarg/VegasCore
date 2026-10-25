/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSuccessorBoundary
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryPrescribedSourceKernel
import Vegas.Game.SourceFailureRecord
import Vegas.Pending.ExclusionAcceptedOutput
import Vegas.Game.AnchoredHonestLaw
import Vegas.Game.AnchoredOpeningClients
import Vegas.Game.IntendedOpeningContinuation

/-! # Genuine clear successor boundaries after honest source steps -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Successor

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

include initialized nativeLaw completes in
/-- A supported stopped endpoint with an intended source decoding is the next
clear scheduler boundary. The actual completion contract rules out exhaustion
while the current event remains pending. -/
theorem recovery_stopped_boundary_of_intended
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil certificate players
      (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).support)
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup leaks final.state = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ∃ anchor : (application setup leaks).Execution,
      final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk anchor.application ∅) ∧
      event ∈ anchor.application.config.cut.completed ∧
      sourceServicePrefix? setup (rank + 1) anchor.application.config = some point ∧
      ReachedBoundary setup leaks horizon scheduler (rank + 1) anchor := by
  exact counted_stopped_boundary_of_intended (setup := setup) (leaks := leaks) (bounds := bounds)
    (completes := Recovery.CompletesPlay.clear_counted_native bounds initialized nativeLaw
    completes) certificate players start current ordered event ready final supported decoded
    intended

variable {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (timely : (runtime setup).AsyncTimely delay bound)

include initialized nativeLaw opportunity inclusion timely completes in
/-- Every supported honest first-callback completion is a genuine clear source
successor boundary, with the source behavioral successor and untouched later events. -/
theorem recovery_firstActivation_honest_successorBoundary
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (info : (N).InfoState who) (observed : (N).infoOf who history.trace = info)
    (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).withLaw info
          (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source who info)))
      (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) history).support) :
    ∃ (target : ProtocolState setup.program) (anchor : (application setup leaks).Execution),
      target ∈ (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point).support ∧
      ProtocolState.Intended setup.program target ∧
      final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk anchor.application ∅) ∧
      event ∈ anchor.application.config.cut.completed ∧
      sourceServicePrefix? setup (rank + 1) anchor.application.config = some target ∧
      ReachedBoundary setup leaks horizon scheduler (rank + 1) anchor := by
  exact counted_firstActivation_honest_successorBoundary (setup := setup) (leaks := leaks) (bounds
    := bounds) (opportunity := Recovery.Opportunity.clear_counted_native bounds initialized
    nativeLaw opportunity) (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds
    initialized nativeLaw inclusion) (timely := timely) (completes :=
    Recovery.CompletesPlay.clear_counted_native bounds initialized nativeLaw completes) wellFormed
    covers capacity source certificate players history current clear event pending never ordered
    decoded intendedPoint info observed final supported

end Successor

end Vegas
