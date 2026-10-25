/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketHonestRecall
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryHonestContinuation
import Vegas.Game.HonestContinuationIntended
import GameTheory.Analysis.Protocol.RestrictionDomination
import Vegas.Game.OnePacketNextEvent

/-! # Honest ready callbacks are recorded under actual recovery service -/

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
  (timely : (runtime setup).AsyncTimely delay bound)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler

variable
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

include initialized nativeLaw opportunity timely inclusion completes in
/-- Honest play from an intended recovery boundary has no unanswered earlier
ready callback at any information state it reaches. -/
theorem recovery_honest_reached_not_late
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (rank : Nat) (start : (E).History) (anchor : (application setup leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ∀ fuel (history : (E).History), history ∈ ((N).runBehavioralFrom
      (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler source) fuel
        start).support → ∀ who, ¬ LateDelivery setup leaks who ((N).infoOf who history.trace) := by
  exact counted_honest_reached_not_late (setup := setup) (leaks := leaks) (bounds := bounds)
    (opportunity := Recovery.Opportunity.clear_counted_native bounds initialized nativeLaw
    opportunity) (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds initialized
    nativeLaw inclusion) (timely := timely) (completes :=
    Recovery.CompletesPlay.clear_counted_native bounds initialized nativeLaw completes) wellFormed
    covers capacity source certificate rank start anchor state boundary point decoded intended

end Vegas
