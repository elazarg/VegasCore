/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedStateBelief
import Vegas.Pending.ExclusionSchedulerSeed

/-! # Actual persistent scheduler seeds at clear recovery information sites -/

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
  (horizon : Nat) {Seed : Type} (prior : PMF Seed)
  (family : Seed → (runtime.reactiveApplication leaks).Scheduler)

local notation "nativeMixture" => ReactiveApplication.schedulerMixture
  (runtime.reactiveApplication leaks) prior family
local notation "recoveryMixture" => ReactiveApplication.schedulerMixture
  (runtime.recoveryApplication leaks) prior
    (fun seed => liftScheduler runtime leaks (family seed))
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler recoveryMixture

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
    (nativeScheduler runtime leaks
      (((runtime.recoveryApplication leaks).schedulerMixture prior
        (fun seed => liftScheduler runtime leaks (family seed))).scheduler))).IsDecisionInfo who
      ((runtime.reactiveApplication leaks).observe who (some reference)))
  (recoveryDecision : (ReactiveApplication.ResponseMenu.information
    (Recovery.onePacketMenu runtime leaks bounds) initial horizon
      (((runtime.recoveryApplication leaks).schedulerMixture prior
        (fun seed => liftScheduler runtime leaks (family seed))).scheduler)).IsDecisionInfo who
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



/-- At a complete clear recovery information site, the actual persistent seed
and projected control have exactly their native conditional joint law. -/
theorem bounded_bayesBelief_seededProjectedState
    (profile : ∀ player, (RecoveryModel).BehavioralPolicy player)
    (positive : 0 < (NativeModel).informationMass
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who
      NativeSite) :
    (((RecoveryModel).bayesBelief profile who RecoverySite
      ((RecoveryMenu).decisionInformationAntichain initial horizon scheduler who RecoverySite)
      (by
        rw [bounded_informationMass_liftedInformationSite runtime leaks bounds initial initialized
          horizon scheduler who reference active valid nativeDecision recoveryDecision profile]
        exact positive)).bind fun history =>
      (match history.1.state with
      | none => prior
      | some current => (recoveryMixture).posterior current.execution.environmentRecall).map
        fun seed => (protocolState runtime leaks history.1.state, seed)) =
      ((((NativeModel).bayesBelief
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who NativeSite
        ((NativeMenu).decisionInformationAntichain (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) who NativeSite) positive).map
            (β := (runtime.reactiveApplication leaks).ProtocolState)
            (fun history => history.1.state)).bind fun state =>
        (match state with
        | none => prior
        | some current => (nativeMixture).posterior current.execution.environmentRecall).map
          (Prod.mk state)) := by
  let draws := fun state : (runtime.reactiveApplication leaks).ProtocolState => match state with
    | none => prior
    | some current => (nativeMixture).posterior current.execution.environmentRecall
  have kernel (state : (runtime.recoveryApplication leaks).ProtocolState) :
      (match state with
      | none => prior
      | some current => (recoveryMixture).posterior current.execution.environmentRecall) =
        draws (protocolState runtime leaks state) := by
    cases state with
    | none => rfl
    | some current =>
        exact schedulerMixture_liftScheduler_posterior runtime leaks prior family
          current.execution.environmentRecall
  have transported := bounded_bayesBelief_projectedState runtime leaks bounds initial initialized
    horizon scheduler who reference active valid nativeDecision recoveryDecision profile positive
  have tagged := congrArg (fun law : PMF (runtime.reactiveApplication leaks).ProtocolState =>
    law.bind fun state => (draws state).map fun seed => (state, seed)) transported
  refine Eq.trans ?_ tagged
  simp only [PMF.bind_map, Function.comp_def]
  apply bind_congr_on_support _
  intro history _
  have mapped := congrArg
    (PMF.map fun seed => (protocolState runtime leaks history.1.state, seed))
      (kernel history.1.state)
  convert mapped using 1
  cases stateEq : history.1.state <;> rfl

include active in
private theorem state_lift_projection
    (history : (RecoveryModel).InformationHistory who RecoverySite.1) :
    liftProtocolState runtime leaks (protocolState runtime leaks history.1.state) =
      history.1.state := by
  have seen := (RecoveryMenu).info initial horizon scheduler who history.1.trace
  change (RecoveryModel).infoOf who history.1.trace =
    (runtime.recoveryApplication leaks).observe who history.1.state at seen
  have observed := seen.symm.trans history.2
  have clear := informationFiber_clear runtime leaks who reference active history.1.state observed
  exact liftProtocolState_protocolState_of_history_clear runtime leaks initial horizon scheduler
    ((RecoveryMenu).toRawHistory initial horizon scheduler history.1).trace clear

/-- The full actual recovery control, including all recalled exclusion records,
and persistent seed have the exact clear-lifted native Bayes joint law. -/
theorem bounded_bayesBelief_seededState
    (profile : ∀ player, (RecoveryModel).BehavioralPolicy player)
    (positive : 0 < (NativeModel).informationMass
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who
      NativeSite) :
    (((RecoveryModel).bayesBelief profile who RecoverySite
      ((RecoveryMenu).decisionInformationAntichain initial horizon scheduler who RecoverySite)
      (by
        rw [bounded_informationMass_liftedInformationSite runtime leaks bounds initial initialized
          horizon scheduler who reference active valid nativeDecision recoveryDecision profile]
        exact positive)).bind fun history =>
      (match history.1.state with
      | none => prior
      | some current => (recoveryMixture).posterior current.execution.environmentRecall).map
        (β := (runtime.recoveryApplication leaks).ProtocolState × Seed)
        (fun seed => (history.1.state, seed))) =
      ((((NativeModel).bayesBelief
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who NativeSite
        ((NativeMenu).decisionInformationAntichain (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) who NativeSite) positive).map
            (β := (runtime.reactiveApplication leaks).ProtocolState)
            (fun history => history.1.state)).bind fun state =>
        (match state with
        | none => prior
        | some current => (nativeMixture).posterior current.execution.environmentRecall).map
          fun seed => (liftProtocolState runtime leaks state, seed)) := by
  have projected := bounded_bayesBelief_seededProjectedState runtime leaks bounds initial
    initialized horizon prior family who reference active valid nativeDecision recoveryDecision
      profile positive
  have lifted := congrArg (PMF.map fun result :
      (runtime.reactiveApplication leaks).ProtocolState × Seed =>
    (liftProtocolState runtime leaks result.1, result.2)) projected
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at lifted
  convert lifted using 1
  apply bind_congr_on_support _
  intro history _
  apply map_congr_on_support _
  intro seed _
  exact Prod.ext (state_lift_projection runtime leaks bounds initial horizon prior family who
    reference active recoveryDecision history).symm rfl

end Vegas.EventGraphRuntime.RecoveryProjection
