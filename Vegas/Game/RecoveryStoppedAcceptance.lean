/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketStoppedAcceptance
import Vegas.Game.RecoveryCountedService
import Vegas.Game.OnePacketDisclosureCompletion
import Vegas.Game.RecoveryStoppedSettlement
import Vegas.Game.OnePacketPendingClear

/-! # Accepted calls through actual recovery stopping boundaries -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (runtime.recoveryApplication leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}
  (inclusion : Recovery.ProtectedInclusion runtime leaks initial horizon recoveryScheduler
    bound)

local notation "scheduler" => RecoveryProjection.nativeScheduler runtime leaks
  recoveryScheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk
    state ∅))

include initialized nativeLaw inclusion in
/-- At actual clear native continuation stops, and at the first exclusion step,
a recorded accepted call either remains pending in its sent configuration
or has performed a successful compiled event step. Only actual
recovery inclusion is assumed; no global native completion contract is used. -/
theorem recovery_accepted_until_config
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (extraStop : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History → Prop)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message) :
    ∀ stop ∈ (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state ∨ extraStop history) start).support,
      ∃ final, stop.state = some final ∧
        (event ∉ final.execution.application.config.cut.completed →
          final.execution.application.config = sent) ∧
        (event ∈ final.execution.application.config.cut.completed →
          ∃ action, final.execution.application.config ∈ (sent.step event ready action).support ∧
            OutputSucceeded final.execution.application.config.store event) := by
  exact counted_accepted_until_config (runtime := runtime) (setup := setup) (leaks := leaks)
    (bounds := bounds)
    (inclusion := Recovery.ProtectedInclusion.clear_counted_native (runtime := runtime) bounds
      initialized nativeLaw
    inclusion) certificate players extraStop ready ordered start current clear invariant atSent
    owned fresh

include initialized nativeLaw inclusion in
/-- Actual recovery completion discharges every premature terminal stop, while
public clarity while pending rules out a premature exclusion stop. Every
stopped continuation therefore performs a successful compiled event step. -/
theorem recovery_accepted_stop_config
    (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message) :
    ∀ stop ∈ (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).support,
      ∃ final action, stop.state = some final ∧
        final.execution.application.config ∈ (sent.step event ready action).support ∧
          OutputSucceeded final.execution.application.config.store event := by
  exact counted_accepted_stop_config (runtime := runtime) (setup := setup) (leaks := leaks)
    (bounds := bounds)
    (inclusion := Recovery.ProtectedInclusion.clear_counted_native (runtime := runtime) bounds
      initialized nativeLaw
    inclusion) (completes := Recovery.CompletesPlay.clear_counted_native (runtime := runtime)
      bounds initialized
    nativeLaw completes) certificate players ready ordered start current clear invariant atSent
    owned fresh

end Vegas
