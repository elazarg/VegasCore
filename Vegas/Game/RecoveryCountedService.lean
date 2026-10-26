/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCountedService
import Vegas.Pending.ExclusionService

/-! # Recovery service at genuine clear native counted prefixes -/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat} {scheduler : (recoveryApplication runtime leaks).Scheduler}

local notation "nativeScheduler" => RecoveryProjection.nativeScheduler runtime leaks
  scheduler

include initialized nativeLaw in
/-- Full recovery service applies at every actual clear native counted prefix. -/
theorem Opportunity.clear_counted_native
    {delay : (graph setup).EventId → Nat}
    (service : Opportunity runtime leaks initial horizon scheduler delay)
    (control : (application setup runtime leaks).Control)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon nativeScheduler).Trace (some
      control))
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅)) :
    OpportunityAt runtime leaks control.execution delay := by
  have raw := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  rw [← nativeLaw] at raw
  exact Opportunity.clear_native runtime leaks initialized service control raw clear

include initialized nativeLaw in
/-- Full recovery service applies at every actual clear native counted prefix. -/
theorem ProtectedInclusion.clear_counted_native
    {bound : (graph setup).EventId → Nat}
    (service : ProtectedInclusion runtime leaks initial horizon scheduler bound)
    (control : (application setup runtime leaks).Control)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon nativeScheduler).Trace (some
      control))
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅)) :
    ProtectedInclusionAt runtime leaks control.execution bound := by
  have raw := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  rw [← nativeLaw] at raw
  exact ProtectedInclusion.clear_native runtime leaks initialized service control raw clear

include initialized nativeLaw in
/-- Full recovery service applies at every actual clear native counted prefix. -/
theorem CompletesPlay.clear_counted_native
    (service : CompletesPlay runtime leaks initial horizon scheduler)
    (control : (application setup runtime leaks).Control)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon nativeScheduler).Trace (some
      control))
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (terminal : (application setup runtime leaks).terminal (some control)) :
    control.execution.application.config.cut.Terminal := by
  have raw := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  rw [← nativeLaw] at raw
  exact CompletesPlay.clear_native runtime leaks initialized service control raw
    clear terminal

end Vegas.EventGraphRuntime.Recovery
