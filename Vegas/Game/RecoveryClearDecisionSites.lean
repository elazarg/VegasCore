/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryClearForced

/-! # Native decision sites represented by clear recovery sites

An actual clear recovery decision has an actual native finite history at the
projected complete input. Both forced predicates therefore refer to the same
native decision site, including histories with zero profile probability.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (RecoveryState (graph setup)))
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (horizon : Nat) (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => MessageBounds.onePacketMenu runtime leaks bounds
local notation "RProtocol" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "NProtocol" => ReactiveApplication.ResponseMenu.protocol
  (MessageBounds.onePacketMenu runtime leaks bounds) (PMF.map RecoveryState.native initial)
  horizon (nativeScheduler runtime leaks scheduler)
local notation "RModel" => model setup runtime leaks bounds initial horizon scheduler
local notation "NModel" => ReactiveApplication.ResponseMenu.information
  (MessageBounds.onePacketMenu runtime leaks bounds) (PMF.map RecoveryState.native initial)
  horizon (nativeScheduler runtime leaks scheduler)

include initialized in
/-- Every actual clear recovery site has a native decision site at its complete
projected input, with exactly the same forced-region classification. -/
theorem exists_nativeInformationSite_of_clear
    [Fintype (RProtocol).History]
    [∀ player, DecidableEq ((RModel).InfoState player)]
    {who : Player} (site : (RModel).InformationSite who)
    (clear : ClearInput runtime leaks site.1) :
    ∃ nativeSite : (NModel).InformationSite who,
      nativeSite.1 = RecoveryProjection.information runtime leaks site.1 ∧
        (Vegas.forcedAgent (runtime := runtime) (NMenu) (initial.map RecoveryState.native) horizon
            (nativeScheduler runtime leaks scheduler) who nativeSite.1 ↔
          ForcedAgent setup runtime leaks bounds initial horizon scheduler ((RModel).agentAt
            site)) := by
  obtain ⟨history, _running, _choice, _legal⟩ := site.2
  have active := InformationSite.active (RModel) site history
  obtain ⟨control, current, actor⟩ := (recoveryApplication runtime leaks).control_of_active
    initial horizon scheduler ((RMenu).toRawHistory initial horizon scheduler history.1) who active
  change history.1.state = some control at current
  have observed := ((RMenu).info initial horizon scheduler who history.1.trace).symm.trans history.2
  rw [current] at observed
  let reference := RecoveryProjection.control runtime leaks control
  have referenceActor : reference.actor = some who := actor
  have projection := observe_projection runtime leaks who (some control)
  change (application setup runtime leaks).observe who (some reference) =
    RecoveryProjection.information runtime leaks
      ((recoveryApplication runtime leaks).observe who (some control)) at projection
  rw [observed] at projection
  have atSite : site.1 = liftInformation runtime leaks
      ((application setup runtime leaks).observe who (some reference)) := by
    rw [projection]
    exact clear.symm
  have clearHistory := informationFiber_clear runtime leaks who reference referenceActor
    history.1.state (((RMenu).info initial horizon scheduler who history.1.trace).symm.trans
      (history.2.trans atSite))
  have nativeState : protocolState runtime leaks history.1.state = some reference := by
    rw [current]
    rfl
  have valid := nativeHistory_record runtime leaks initial initialized horizon scheduler
    ((RMenu).toRawTrace initial horizon scheduler history.1.trace) clearHistory reference
      nativeState
  obtain ⟨projected, same⟩ := exists_nativeBoundedHistory runtime leaks bounds initial
    initialized horizon scheduler history.1 clearHistory
  have states := congrArg ExecutionProtocol.History.state same
  change projected.state = protocolState runtime leaks history.1.state at states
  have projectedState := states.trans nativeState
  have seen : (NModel).infoOf who projected.trace =
      RecoveryProjection.information runtime leaks site.1 :=
    ((NMenu).info (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler) who projected.trace).trans
        ((congrArg ((application setup runtime leaks).observe who) projectedState).trans projection)
  have nativeActive : (NProtocol).active projected.state who := by
    change (application setup runtime leaks).actor projected.state = some who
    rw [projectedState]
    exact referenceActor
  have nativeRunning : ¬ (NProtocol).terminal projected.state := by
    change ¬ (application setup runtime leaks).terminal projected.state
    rw [projectedState]
    intro stopped
    have impossible := referenceActor.symm.trans stopped.2
    cases impossible
  obtain ⟨nativeSite, nativeInput⟩ := (NModel).exists_informationSite_of_active who projected
    nativeRunning nativeActive
  have siteInput := nativeInput.trans seen
  refine ⟨nativeSite, siteInput, ?_⟩
  have matching := siteInput.trans projection.symm
  rw [matching]
  exact forcedAgent_iff_of_clearInput setup runtime leaks bounds initial initialized horizon
    scheduler
    who reference referenceActor valid site atSite

end Vegas.RecoveryOnePacket
