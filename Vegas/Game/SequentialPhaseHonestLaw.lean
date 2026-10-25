/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketInitializedLaw
import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.SequentialPhaseNativeComparison

/-! # Honest native source laws under physical singleton phase service -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : PhaseService.Opportunity (runtime setup) leaks (initialLaw setup) horizon
    scheduler delay)
  (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon
    scheduler bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : PhaseService.CompletesPlay (runtime setup) leaks (initialLaw setup) horizon
    scheduler)

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (recoveryScheduler setup leaks scheduler)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (nativeScheduler)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (oldLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)
local notation "NativeModel" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup)
  horizon (nativeScheduler)
local notation "NativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (oldLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

include opportunity inclusion timely completes in
theorem honest_boundary_readout_law
    (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) :
    ∀ rank (start : (E).History) (execution : (application setup (oldLeaks)).Execution),
      start.state = some ⟨horizon - execution.environmentRecall.length, none, execution⟩ →
      ReachedBoundary setup (oldLeaks) horizon (nativeScheduler) rank execution →
      ∀ point, sourceServicePrefix? setup rank execution.application.config = some point →
        ProtocolState.Intended setup.program point →
      ((N).runBehavioralTerminalFrom certificate
        (honestProfile setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
          (nativeScheduler) source) start).map
          (fun final => sourceReadout setup (oldLeaks) final.state) =
        sourceContinuation setup (setup.intendedOpeningProfile source.strategy) rank
          execution.application.config  := by
  exact counted_honest_boundary_readout_law (setup := setup) (leaks := oldLeaks) (bounds := bounds)
    (opportunity := fun control trace clear =>
      PhaseService.Opportunity.clear_native_counted setup leaks bounds horizon scheduler delay
        opportunity trace clear)
    (inclusion := fun control trace clear =>
      PhaseService.ProtectedInclusion.clear_native_counted setup leaks bounds horizon scheduler
        bound inclusion trace clear)
    (timely := timely)
    (completes := fun control trace clear terminal =>
      PhaseService.CompletesPlay.clear_native_counted setup leaks bounds horizon scheduler
        completes trace clear terminal)
    wellFormed covers capacity source certificate

include opportunity inclusion timely completes in
theorem honest_reached_not_late
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (rank : Nat) (start : (E).History) (anchor : (application setup (oldLeaks)).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup (oldLeaks) horizon (nativeScheduler) rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ∀ fuel (history : (E).History), history ∈ ((N).runBehavioralFrom
      (honestProfile setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (nativeScheduler) source) fuel
        start).support → ∀ who, ¬ LateDelivery setup (oldLeaks) who ((N).infoOf who
          history.trace)  := by
  exact counted_honest_reached_not_late (setup := setup) (leaks := oldLeaks) (bounds := bounds)
    (opportunity := fun control trace clear =>
      PhaseService.Opportunity.clear_native_counted setup leaks bounds horizon scheduler delay
        opportunity trace clear)
    (inclusion := fun control trace clear =>
      PhaseService.ProtectedInclusion.clear_native_counted setup leaks bounds horizon scheduler
        bound inclusion trace clear)
    (timely := timely)
    (completes := fun control trace clear terminal =>
      PhaseService.CompletesPlay.clear_native_counted setup leaks bounds horizon scheduler
        completes trace clear terminal)
    wellFormed covers capacity source certificate rank start anchor state boundary point
      decoded intended

include opportunity inclusion timely completes in
theorem honest_initialized_readout_law
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    (((NativeModel).runBehavioralTerminalFrom certificate
      (honestProfile setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (nativeScheduler) source)
        (NativeProtocol).initHistory).map (fun final => sourceReadout setup (oldLeaks)
          final.state)) =
      (setup.intendedModel.runBehavioral source.strategy
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state)  := by
  exact counted_honest_initialized_readout_law (setup := setup) (leaks := oldLeaks) (bounds
    := bounds)
    (opportunity := fun control trace clear =>
      PhaseService.Opportunity.clear_native_counted setup leaks bounds horizon scheduler delay
        opportunity trace clear)
    (inclusion := fun control trace clear =>
      PhaseService.ProtectedInclusion.clear_native_counted setup leaks bounds horizon scheduler
        bound inclusion trace clear)
    (timely := timely)
    (completes := fun control trace clear terminal =>
      PhaseService.CompletesPlay.clear_native_counted setup leaks bounds horizon scheduler
        completes trace clear terminal)
    wellFormed covers capacity source certificate

include opportunity inclusion timely completes in
theorem honest_initialized_not_late
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    ∀ fuel history, history ∈ ((NativeModel).runBehavioralFrom
      (honestProfile setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (nativeScheduler) source) fuel
        (NativeProtocol).initHistory).support →
      ∀ who, ¬ LateDelivery setup (oldLeaks) who ((NativeModel).infoOf who history.trace)  := by
  exact counted_honest_initialized_not_late (setup := setup) (leaks := oldLeaks) (bounds := bounds)
    (opportunity := fun control trace clear =>
      PhaseService.Opportunity.clear_native_counted setup leaks bounds horizon scheduler delay
        opportunity trace clear)
    (inclusion := fun control trace clear =>
      PhaseService.ProtectedInclusion.clear_native_counted setup leaks bounds horizon scheduler
        bound inclusion trace clear)
    (timely := timely)
    (completes := fun control trace clear terminal =>
      PhaseService.CompletesPlay.clear_native_counted setup leaks bounds horizon scheduler
        completes trace clear terminal)
    wellFormed covers capacity source certificate

include opportunity inclusion timely completes in
theorem honest_initialized_intended
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    ∀ fuel history, history ∈ ((NativeModel).runBehavioralFrom
      (honestProfile setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (nativeScheduler) source) fuel
        (NativeProtocol).initHistory).support →
      ∀ control : (application setup (oldLeaks)).Control, history.state = some control →
        ∃ point, decodedPoint setup control.execution.application.config = some point ∧
          ProtocolState.Intended setup.program point  := by
  exact counted_honest_initialized_intended (setup := setup) (leaks := oldLeaks) (bounds := bounds)
    (opportunity := fun control trace clear =>
      PhaseService.Opportunity.clear_native_counted setup leaks bounds horizon scheduler delay
        opportunity trace clear)
    (inclusion := fun control trace clear =>
      PhaseService.ProtectedInclusion.clear_native_counted setup leaks bounds horizon scheduler
        bound inclusion trace clear)
    (timely := timely)
    (completes := fun control trace clear terminal =>
      PhaseService.CompletesPlay.clear_native_counted setup leaks bounds horizon scheduler
        completes trace clear terminal)
    wellFormed covers capacity source certificate

end Vegas.SequentialPhase
