/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPrescribedSourceKernel
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryStoppedSourceLaw
import Vegas.Game.OnePacketDebtFreeResponse

/-! # Source-value kernels of prescribed play under actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication runtime leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity runtime leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion runtime leaks initial horizon recoveryScheduler
    bound)
  (timely : runtime.AsyncTimely delay bound)
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


include initialized nativeLaw opportunity inclusion timely completes in
/-- Installing the source-main choice at an actual clear first callback gives the
source behavioral step at its decoded intended point. Both binding and disclosure
use the actual recovery service, with arbitrary continuation policies. -/
theorem recovery_firstActivation_honest_sourceLaw
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup runtime leaks who (some (execution.recall who,
      execution.observe (application setup runtime leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup runtime leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (info : (N).InfoState who) (observed : (N).infoOf who history.trace = info) :
    ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).withLaw info
          (honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler source who
            info)))
      (fun stop => LateStopped setup runtime leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) history).map
        (fun stop => nativeDecodedState setup runtime leaks stop.state) =
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point).map some := by
  exact counted_firstActivation_honest_sourceLaw (runtime := runtime) (setup := setup) (leaks :=
    leaks) (bounds :=
    bounds) (opportunity := Recovery.Opportunity.clear_counted_native (runtime := runtime) bounds
      initialized nativeLaw
    opportunity) (inclusion := Recovery.ProtectedInclusion.clear_counted_native (runtime :=
      runtime) bounds initialized
    nativeLaw inclusion) (timely := timely) (completes :=
    Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds initialized nativeLaw
      completes) wellFormed
    covers capacity source certificate players history current clear event pending never ordered
    decoded intendedPoint info observed


end Vegas
