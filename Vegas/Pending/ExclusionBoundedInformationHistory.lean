/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedBelief
import Vegas.Pending.ExclusionBoundedHistory

/-! # Complete finite information histories before public exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (RecoveryState graph))
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
  (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeMenu" => MessageBounds.onePacketMenu runtime leaks bounds
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NativeModel" => ReactiveApplication.ResponseMenu.information
  (NativeMenu) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.ResponseMenu.information
  (RecoveryMenu) initial horizon scheduler
local notation "NativeRaw" => ReactiveApplication.information
  (reactiveApplication runtime leaks) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryRaw" => ReactiveApplication.information
  (recoveryApplication runtime leaks) initial horizon scheduler

variable (who : Player) (reference : (runtime.reactiveApplication leaks).Control)
  (active : reference.actor = some who)
  (valid : PublicExclusionRecord (⟨reference.execution.application, ∅⟩ : RecoveryState graph))
  (nativeDecision : (ReactiveApplication.ResponseMenu.information
    (MessageBounds.onePacketMenu runtime leaks bounds) (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler)).IsDecisionInfo who
      ((runtime.reactiveApplication leaks).observe who (some reference)))
  (recoveryDecision : (ReactiveApplication.ResponseMenu.information
    (Recovery.onePacketMenu runtime leaks bounds) initial horizon scheduler).IsDecisionInfo who
      (liftInformation runtime leaks
        ((runtime.reactiveApplication leaks).observe who (some reference))))

local notation "NativeSite" => Subtype.mk
  (p := InformationModel.IsDecisionInfo (NativeModel) who)
  (ReactiveApplication.observe (reactiveApplication runtime leaks) who (some reference))
  nativeDecision
local notation "RecoverySite" => Subtype.mk
  (p := InformationModel.IsDecisionInfo (RecoveryModel) who)
  (liftInformation runtime leaks
    (ReactiveApplication.observe (reactiveApplication runtime leaks) who (some reference)))
  recoveryDecision

include initialized active valid in
private theorem exists_boundedInformationHistory
    (history : (RecoveryModel).InformationHistory who RecoverySite.1) :
    ∃ projected : (NativeModel).InformationHistory who NativeSite.1,
      (NativeMenu).toRawHistory (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) projected.1 =
        (informationHistoryEquiv runtime leaks initial initialized horizon scheduler who reference
          active valid ((RecoveryMenu).rawInformationHistory initial horizon scheduler who
            RecoverySite history)).1 := by
  let raw := (RecoveryMenu).rawInformationHistory initial horizon scheduler who RecoverySite history
  let target := informationHistoryEquiv runtime leaks initial initialized horizon scheduler who
    reference active valid raw
  have same := raw.2
  simp only [ReactiveApplication.information, ReactiveApplication.info] at same
  have clear := informationFiber_clear runtime leaks who reference active raw.1.state same
  obtain ⟨projected, equal⟩ := exists_nativeBoundedHistory runtime leaks bounds initial initialized
    horizon scheduler history.1 clear
  have rawEq : (NativeMenu).toRawHistory (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler) projected = target.1 := equal
  have seen : (NativeRaw).infoOf who
      ((NativeMenu).toRawHistory (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) projected).trace = NativeSite.1 := by
    rw [rawEq]
    exact target.2
  exact ⟨⟨projected, ((NativeMenu).info_toRawTrace (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler) who projected.trace).symm.trans seen⟩, rawEq⟩

include initialized active valid in
/-- The actual finite native information history corresponding to an entire
clear recovery information history, including zero-probability histories. -/
def boundedInformationHistory
    (history : (RecoveryModel).InformationHistory who RecoverySite.1) :
    (NativeModel).InformationHistory who NativeSite.1 :=
  (exists_boundedInformationHistory runtime leaks bounds initial initialized horizon scheduler
    who reference active valid nativeDecision recoveryDecision history).choose

/-- The finite projection retains exactly the existing complete raw projection. -/
theorem boundedInformationHistory_raw
    (history : (RecoveryModel).InformationHistory who RecoverySite.1) :
    (NativeMenu).toRawHistory (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler)
        (boundedInformationHistory runtime leaks bounds initial initialized horizon scheduler who
          reference active valid nativeDecision recoveryDecision history).1 =
      (informationHistoryEquiv runtime leaks initial initialized horizon scheduler who reference
        active valid ((RecoveryMenu).rawInformationHistory initial horizon scheduler who
          RecoverySite history)).1 :=
  (exists_boundedInformationHistory runtime leaks bounds initial initialized horizon scheduler
    who reference active valid nativeDecision recoveryDecision history).choose_spec

/-- Finite clear-fiber projection preserves the complete native control. -/
theorem boundedInformationHistory_state
    (history : (RecoveryModel).InformationHistory who RecoverySite.1) :
    (boundedInformationHistory runtime leaks bounds initial initialized horizon scheduler who
      reference active valid nativeDecision recoveryDecision history).1.state =
        protocolState runtime leaks history.1.state := by
  exact congrArg History.state (boundedInformationHistory_raw runtime leaks bounds initial
    initialized horizon scheduler who reference active valid nativeDecision recoveryDecision
    history)

end Vegas.EventGraphRuntime.RecoveryProjection
