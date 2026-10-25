/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketHonestContinuation
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryBoundaryWaiting
import Vegas.Game.RecoveryTerminalSourceLaw
import Vegas.Game.RecoveryChanceStoppedLaw

/-! # Honest source continuation on the actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

include initialized nativeLaw opportunity inclusion timely completes in
/-- Honest finite-menu play from an intended source boundary has the source
continuation law under actual recovery service and completion. -/
theorem recovery_honest_boundary_readout_law
    (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) :
    ∀ rank (start : (E).History) (execution : (application setup leaks).Execution),
      start.state = some ⟨horizon - execution.environmentRecall.length, none, execution⟩ →
      ReachedBoundary setup leaks horizon scheduler rank execution →
      ∀ point, sourceServicePrefix? setup rank execution.application.config = some point →
        ProtocolState.Intended setup.program point →
      ((N).runBehavioralTerminalFrom certificate
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler source) start).map
          (fun final => sourceReadout setup leaks final.state) =
        sourceContinuation setup (setup.intendedOpeningProfile source.strategy) rank
          execution.application.config := by
  exact counted_honest_boundary_readout_law (setup := setup) (leaks := leaks) (bounds := bounds)
    (opportunity := Recovery.Opportunity.clear_counted_native bounds initialized nativeLaw
    opportunity) (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds initialized
    nativeLaw inclusion) (timely := timely) (completes :=
    Recovery.CompletesPlay.clear_counted_native bounds initialized nativeLaw completes) wellFormed
    covers capacity source certificate

end Vegas
