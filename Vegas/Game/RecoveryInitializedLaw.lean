/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketInitializedLaw
import Vegas.Game.OnePacketComparisonRetention
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryComparisonRetention
import Vegas.Game.SourceServiceSiteBridge

/-! # Initialized source laws under the actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {horizon : Nat} {scheduler : (application setup leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler

variable {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "NativeModel" => onePacketModel setup leaks bounds (initialLaw setup) horizon
  nativeScheduler
local notation "NativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon nativeScheduler

include initialized nativeLaw opportunity inclusion timely completes in
/-- Actual recovery service makes initialized honest native play preserve the
entire intended terminal store law, with its private setup draw. -/
theorem recovery_honest_initialized_readout_law
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    (((NativeModel).runBehavioralTerminalFrom certificate
      (honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source)
        (NativeProtocol).initHistory).map (fun final => sourceReadout setup leaks final.state)) =
      (setup.intendedModel.runBehavioral source.strategy
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state) := by
  exact counted_honest_initialized_readout_law (setup := setup) (leaks := leaks) (bounds :=
    bounds) (opportunity := Recovery.Opportunity.clear_counted_native bounds initialized nativeLaw
    opportunity) (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds initialized
    nativeLaw inclusion) (timely := timely) (completes :=
    Recovery.CompletesPlay.clear_counted_native bounds initialized nativeLaw completes) wellFormed
    covers capacity source certificate

include initialized nativeLaw opportunity inclusion timely completes in
/-- Every initialized supported honest native input is a first activation or
already has its event packet recorded. -/
theorem recovery_honest_initialized_not_late
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    ∀ fuel history, history ∈ ((NativeModel).runBehavioralFrom
      (honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source) fuel
        (NativeProtocol).initHistory).support →
      ∀ who, ¬ LateDelivery setup leaks who ((NativeModel).infoOf who history.trace) := by
  exact counted_honest_initialized_not_late (setup := setup) (leaks := leaks) (bounds := bounds)
    (opportunity := Recovery.Opportunity.clear_counted_native bounds initialized nativeLaw
    opportunity) (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds initialized
    nativeLaw inclusion) (timely := timely) (completes :=
    Recovery.CompletesPlay.clear_counted_native bounds initialized nativeLaw completes) wellFormed
    covers capacity source certificate

include initialized nativeLaw opportunity inclusion timely completes in
/-- Every initialized honest native execution decodes to an intended source
point under the actual recovery service. -/
theorem recovery_honest_initialized_intended
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    ∀ fuel history, history ∈ ((NativeModel).runBehavioralFrom
      (honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source) fuel
        (NativeProtocol).initHistory).support →
      ∀ control : (application setup leaks).Control, history.state = some control →
        ∃ point, decodedPoint setup control.execution.application.config = some point ∧
          ProtocolState.Intended setup.program point := by
  exact counted_honest_initialized_intended (setup := setup) (leaks := leaks) (bounds := bounds)
    (opportunity := Recovery.Opportunity.clear_counted_native bounds initialized nativeLaw
    opportunity) (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds initialized
    nativeLaw inclusion) (timely := timely) (completes :=
    Recovery.CompletesPlay.clear_counted_native bounds initialized nativeLaw completes) wellFormed
    covers capacity source certificate

end Vegas

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)

/-- The unchanged common recovery weights retain initialized honest native
play, including its setup draw, under actual recovery service. -/
theorem nativeComparison_dominatesHonestFrom_initialized [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (certificate : (NP).WellFoundedHistories) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
      (sequence n) (slotRetention (scale n))
      (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n) (NP).initHistory := by
  exact OnePacketComparison.assembled_dominatesHonestFrom_initialized setup leaks bounds
    horizon (NativeScheduler)
    wellFormed covers capacity sequence scale positive le_one
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
    (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
      weights)
    (nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence scale positive
      le_one weights) n
    (Recovery.Opportunity.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) opportunity)
    (Recovery.ProtectedInclusion.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) inclusion)
    timely
    (Recovery.CompletesPlay.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) completes)
    certificate

end Vegas.RecoveryOnePacket
