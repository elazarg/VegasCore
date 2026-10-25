/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.RecoverySuccessorBoundary

/-! # Counted native terminal completion from physical singleton phases -/

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

/-- Physical phase completion settles a genuinely counted native terminal
whose unchanged configuration still decodes to an intended source point. -/
theorem phase_terminal_completed_of_decodedIntended
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (phaseInitial) horizon scheduler)
    {rank : Nat} {sent : (graph setup).Config} (ordered : sent.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    (intended : ProtocolState.Intended setup.program point)
    (event : (graph setup).EventId) (final : (native).Control)
    (trace : (onePacketProtocol setup (RecoveryLeaks) bounds horizon (nativeScheduler)).Trace
      (some final))
    (ended : (native).terminal (some final))
    (same : final.execution.application.config = sent) :
    event ∈ final.execution.application.config.cut.completed := by
  have finalDecoded : decodedPoint setup final.execution.application.config = some point := by
    rw [decodedPoint_eq_of_isPrefix (show
      final.execution.application.config.cut.IsPrefix rank by rw [same]; exact ordered), same]
    exact decoded
  have clear := exclusionEvidence_of_decodedIntended
    ((bounds.onePacketMenu (runtime setup) (RecoveryLeaks)).toRawTrace (initialLaw setup) horizon
      (nativeScheduler) trace) finalDecoded intended
  have complete := PhaseService.CompletesPlay.clear_native_counted setup leaks bounds horizon
    scheduler completes trace clear ended
  rw [complete]
  exact Finset.mem_univ _

end Vegas
