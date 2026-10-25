/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketStoppedSettlement
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryProtectedCalls
import Vegas.Game.OnePacketFirstActivation
import Vegas.Pending.ExclusionStoppedBoundary

/-! # Fresh-call settlement on actual stopped native continuations -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon scheduler bound)

local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  scheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "protocol" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup)
  horizon nativeScheduler
local notation "model" => ReactiveApplication.ResponseMenu.information menu (initialLaw setup)
  horizon nativeScheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅))

include initialized nativeLaw inclusion in
/-- Actual recovery inclusion settles recorded fresh one-packet calls at every
native continuation endpoint stopped at public exclusion or an earlier condition.
Settlement is asserted only on these supported stops, including the first exit. -/
theorem recovery_stopped_freshCall_receipt
    (certificate : (protocol).WellFoundedHistories)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (extraStop : (protocol).History → Prop)
    (start : (protocol).History) (current : (application setup leaks).Control)
    (state : start.state = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (who : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (call : FreshCall setup leaks who event bound entry message) :
    ∀ stopped ∈ ((model).runBehavioralUntil certificate profile
        (fun history => ¬ Clear history.state ∨ extraStop history) start).support,
      ∀ final, stopped.state = some final → RecordsEntry setup leaks who entry (some final) →
        event ∈ final.execution.application.config.cut.completed →
          (message.id, true) ∈ final.execution.receipts := by
  exact counted_stopped_freshCall_receipt (setup := setup) (leaks := leaks) (bounds := bounds)
    (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds initialized nativeLaw
    inclusion) certificate profile extraStop start current state clear who event owned entry
    message call

end Vegas
