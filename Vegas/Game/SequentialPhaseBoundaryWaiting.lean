/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.OnePacketBoundaryWaiting

/-! # First native owner callbacks from physical singleton phase service -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)

local notation "RecoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks
  (sequentialRuntimePhasePlan setup.program)
local notation "RecoveryScheduler" => SequentialPhaseSchedulerInformation.scheduler setup.program
  (runtime setup) leaks (RecoveryLeaks) scheduler
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup)
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "native" => application setup (RecoveryLeaks)
local notation "phaseInitial" => PMF.map
  (PhaseRuntimeState.initial (sequentialRuntimePhasePlan setup.program))
  (PMF.map setup.eventInputs setup.initialLaw)

local notation "Menu" => bounds.onePacketMenu (runtime setup) (RecoveryLeaks)

/-- Physical singleton phase service reaches the first native owner callback
from every actual clear source boundary, preserving configuration and own recall. -/
theorem phase_boundary_firstActivation {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (phaseInitial) horizon scheduler
      delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (phaseInitial) horizon scheduler)
    (certificate : ((Menu).protocol (initialLaw setup) horizon
      (nativeScheduler)).WellFoundedHistories)
    (players : ∀ player, ((Menu).information (initialLaw setup) horizon
      (nativeScheduler)).BehavioralPolicy player)
    (start : ((Menu).protocol (initialLaw setup) horizon (nativeScheduler)).History)
    {rank : Nat} {execution : (native).Execution}
    (current : start.state =
      some ⟨horizon - execution.environmentRecall.length, none, execution⟩)
    (boundary : ReachedBoundary setup (RecoveryLeaks) horizon (nativeScheduler) rank execution)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId) (atRank : event.val = rank)
    (owned : (graph setup).actor? event = some owner) :
    ∀ stopped ∈ (((Menu).information (initialLaw setup) horizon
      (nativeScheduler)).runBehavioralUntil certificate players
        (fun history => (native).actor history.state = some owner) start).support,
      ∃ (remaining : Nat) (anchor : (native).Execution),
        stopped.state = some ⟨remaining, some owner, anchor⟩ ∧
        anchor.application.config = execution.application.config ∧
        ExclusionEvidence 0 ∅ (RecoveryState.mk anchor.application ∅) ∧
        anchor.recall owner = execution.recall owner ∧
        pendingEvent setup (RecoveryLeaks) owner
          (some (anchor.recall owner,
            anchor.observe (native) owner)) = some event ∧
        ∀ entry ∈ anchor.recall owner, ¬ ActivatedAt setup (RecoveryLeaks) owner event entry := by
  exact counted_boundary_firstActivation
    (fun _ trace clear => PhaseService.Opportunity.clear_native_counted setup leaks bounds horizon
      scheduler delay opportunity trace clear) timely
    (fun _ trace clear terminal => PhaseService.CompletesPlay.clear_native_counted setup leaks
      bounds horizon scheduler completes trace clear terminal) certificate players start current
    boundary clear decoded intendedPoint owner event atRank owned

end Vegas
