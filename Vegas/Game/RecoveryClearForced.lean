/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryOnePacketComponents
import Vegas.Pending.ExclusionBoundedHistory

/-! # The forced region at clear recovery decision inputs

The actual finite clear-history correspondences identify forced witnesses on
both sides. Every native history in a corresponding decision fiber is publicly
clear, as witnessed by the complete current public record.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (RecoveryState (graph setup)))
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (horizon : Nat) (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => MessageBounds.onePacketMenu (runtime setup) leaks bounds
local notation "RProtocol" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) initial horizon scheduler
local notation "NProtocol" => ReactiveApplication.ResponseMenu.protocol
  (MessageBounds.onePacketMenu (runtime setup) leaks bounds) (PMF.map RecoveryState.native initial)
  horizon (nativeScheduler (runtime setup) leaks scheduler)
local notation "RModel" => model setup leaks bounds initial horizon scheduler
local notation "NModel" => ReactiveApplication.ResponseMenu.information
  (MessageBounds.onePacketMenu (runtime setup) leaks bounds) (PMF.map RecoveryState.native initial)
  horizon (nativeScheduler (runtime setup) leaks scheduler)

include initialized in
/-- At corresponding clear decision inputs, actual forced witnesses exist in
exactly the same cases in the native and recovery finite presentations. -/
theorem forcedAgent_iff_of_clearInput
    [Fintype (RProtocol).History]
    [∀ player, DecidableEq ((RModel).InfoState player)]
    (who : Player) (reference : (application setup leaks).Control)
    (active : reference.actor = some who)
    (valid : PublicExclusionRecord
      (RecoveryState.mk reference.execution.application ∅ : RecoveryState (graph setup)))
    (site : (RModel).InformationSite who)
    (atSite : site.1 = liftInformation (runtime setup) leaks
      ((application setup leaks).observe who (some reference))) :
    Vegas.forcedAgent (NMenu) (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler) who
        ((application setup leaks).observe who (some reference)) ↔
      ForcedAgent setup leaks bounds initial horizon scheduler ((RModel).agentAt site) := by
  constructor
  · rintro ⟨history, seen, forced⟩
    refine ⟨?_, ?_⟩
    · rw [atSite]
      exact clearInput_lift (runtime setup) leaks _
    have observed := ((NMenu).info (initial.map RecoveryState.native) horizon
      (nativeScheduler (runtime setup) leaks scheduler) who history.trace).symm.trans seen
    have clear := informationFiber_record (runtime setup) leaks initial initialized horizon
      scheduler who reference active valid
      ((NMenu).toRawHistory (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler) history) observed
    obtain ⟨lifted, same⟩ := exists_recoveryBoundedHistory (runtime setup) leaks bounds initial
      initialized horizon scheduler history clear
    have liftedInfo : (RModel).infoOf who lifted.trace =
        liftInformation (runtime setup) leaks
          ((application setup leaks).observe who (some reference)) := by
      rw [← (RMenu).info_toRawTrace initial horizon scheduler who lifted.trace]
      change (ReactiveApplication.information (recoveryApplication (runtime setup) leaks)
        initial horizon scheduler).infoOf who
          ((RMenu).toRawHistory initial horizon scheduler lifted).trace = _
      rw [same, infoOf_recoveryHistory]
      exact congrArg (liftInformation (runtime setup) leaks)
        (((NMenu).info_toRawTrace (initial.map RecoveryState.native) horizon
          (nativeScheduler (runtime setup) leaks scheduler) who history.trace).trans seen)
    have states := congrArg ExecutionProtocol.History.state same
    change lifted.state = liftProtocolState (runtime setup) leaks history.state at states
    refine ⟨⟨lifted, liftedInfo.trans atSite.symm⟩, ?_⟩
    change Vegas.ForcedState setup leaks who
      (protocolState (runtime setup) leaks lifted.state)
    rw [states, protocolState_liftProtocolState]
    exact forced
  · rintro ⟨_canonical, history, forced⟩
    have observed := ((RMenu).info initial horizon scheduler who history.1.trace).symm.trans
      (history.2.trans atSite)
    have clear := informationFiber_clear (runtime setup) leaks who reference active
      history.1.state observed
    obtain ⟨projected, same⟩ := exists_nativeBoundedHistory (runtime setup) leaks bounds initial
      initialized horizon scheduler history.1 clear
    have projectedInfo : (NModel).infoOf who projected.trace =
        (application setup leaks).observe who (some reference) := by
      rw [← (NMenu).info_toRawTrace (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler) who projected.trace]
      change (ReactiveApplication.information (reactiveApplication (runtime setup) leaks)
        (initial.map RecoveryState.native) horizon
        (nativeScheduler (runtime setup) leaks scheduler)).infoOf who
          ((NMenu).toRawHistory (initial.map RecoveryState.native) horizon
            (nativeScheduler (runtime setup) leaks scheduler) projected).trace = _
      rw [same, infoOf_nativeHistory]
      have rawSeen := ((RMenu).info_toRawTrace initial horizon scheduler who history.1.trace).trans
        (history.2.trans atSite)
      exact (congrArg (RecoveryProjection.information (runtime setup) leaks) rawSeen).trans
        (information_liftInformation (runtime setup) leaks _)
    have states := congrArg ExecutionProtocol.History.state same
    change projected.state = protocolState (runtime setup) leaks history.1.state at states
    refine ⟨projected, projectedInfo, ?_⟩
    rw [states]
    exact forced

end Vegas.RecoveryOnePacket
