/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedBelief

/-! # Complete control laws at actual clear recovery information sites -/

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


/-- Clear finite recovery Bayes beliefs project exactly to the standard native
Bayes law on complete current controls. -/
theorem bounded_bayesBelief_projectedState
    (profile : ∀ player, (RecoveryModel).BehavioralPolicy player)
    (positive : 0 < (NativeModel).informationMass
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who
      NativeSite) :
    ((RecoveryModel).bayesBelief profile who RecoverySite
      ((RecoveryMenu).decisionInformationAntichain initial horizon scheduler who RecoverySite)
      (by
        rw [bounded_informationMass_liftedInformationSite runtime leaks bounds initial initialized
          horizon scheduler who reference active valid nativeDecision recoveryDecision profile]
        exact positive)).map
      (fun history => protocolState runtime leaks history.1.state) =
      ((NativeModel).bayesBelief
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who NativeSite
        ((NativeMenu).decisionInformationAntichain (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) who NativeSite) positive).map
        (fun history => history.1.state) := by
  have compared := bounded_bayesBelief_liftedInformationSite runtime leaks bounds initial
    initialized horizon scheduler who reference active valid nativeDecision recoveryDecision
      profile positive
  have mapped := congrArg (PMF.map fun history :
      (NativeRaw).InformationHistory who
        ((runtime.reactiveApplication leaks).observe who (some reference)) =>
    history.1.state) compared
  simp only [PMF.map_comp, Function.comp_def] at mapped
  convert mapped using 1 <;> rfl

end Vegas.EventGraphRuntime.RecoveryProjection
