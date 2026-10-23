/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionClearReach

/-! # Exact Bayes beliefs before public exclusion

The complete information-fiber bijection preserves actual history reach
weights. Summation and normalization therefore preserve information masses and
Bayes beliefs. No projection of continuations after exclusion is asserted.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (RecoveryState graph))
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
  (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeModel" => ReactiveApplication.information
  (reactiveApplication runtime leaks) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.information
  (recoveryApplication runtime leaks) initial horizon scheduler

omit [Fintype Player] in
include initialized in
/-- A genuine native decision with no public exclusion evidence lifts to a
genuine recovery decision with exactly the lifted full information input. -/
def liftedInformationSite (who : Player)
    (reference : (runtime.reactiveApplication leaks).Control)
    (active : reference.actor = some who)
    (valid : PublicExclusionRecord (⟨reference.execution.application, ∅⟩ : RecoveryState graph))
    (decision : (NativeModel).IsDecisionInfo who
      ((runtime.reactiveApplication leaks).observe who (some reference))) :
    (RecoveryModel).InformationSite who :=
  ⟨liftInformation runtime leaks ((runtime.reactiveApplication leaks).observe who (some reference)),
    by
      obtain ⟨history, running, action, permitted⟩ := decision
      let equivalent := informationHistoryEquiv runtime leaks initial initialized horizon scheduler
        who reference active valid
      let lifted := equivalent.symm history
      refine ⟨lifted, ?_, liftAction runtime leaks action, ?_⟩
      · change ¬ (runtime.recoveryApplication leaks).terminal
          (liftProtocolState runtime leaks history.1.state)
        exact fun ended => running ((terminal_liftProtocolState runtime leaks history.1.state).mp
          ended)
      · change (some (liftAction runtime leaks action)).isSome =
          (liftInformation runtime leaks
            ((runtime.reactiveApplication leaks).observe who (some reference))).isSome
        have chosen := permitted
        change (some action).isSome =
          ((runtime.reactiveApplication leaks).observe who (some reference)).isSome at chosen
        simpa only [liftInformation, Option.isSome_map, Option.isSome_some] using chosen⟩

variable (who : Player) (reference : (runtime.reactiveApplication leaks).Control)
  (active : reference.actor = some who)
  (valid : PublicExclusionRecord (⟨reference.execution.application, ∅⟩ : RecoveryState graph))
  (decision : ((runtime.reactiveApplication leaks).information
    (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler)).IsDecisionInfo who
      ((runtime.reactiveApplication leaks).observe who (some reference)))

local notation "NativeSite" => Subtype.mk
  (p := InformationModel.IsDecisionInfo (NativeModel) who)
  (ReactiveApplication.observe (reactiveApplication runtime leaks) who (some reference)) decision
local notation "RecoverySite" => liftedInformationSite runtime leaks initial initialized horizon
  scheduler who reference active valid decision

/-- Summing actual paired reach weights gives equal probabilities of the
complete information event in the native and recovery games. -/
theorem informationMass_liftedInformationSite
    (profile : ∀ player, (RecoveryModel).BehavioralPolicy player) :
    (RecoveryModel).informationMass profile who RecoverySite =
      (NativeModel).informationMass
        (nativeProfile runtime leaks initial horizon scheduler profile) who NativeSite := by
  change (∑' history : (RecoveryModel).InformationHistory who
      (liftInformation runtime leaks ((runtime.reactiveApplication leaks).observe who
        (some reference))), (RecoveryModel).historyReachWeight profile history.1) =
    ∑' history : (NativeModel).InformationHistory who
      ((runtime.reactiveApplication leaks).observe who (some reference)),
      (NativeModel).historyReachWeight
        (nativeProfile runtime leaks initial horizon scheduler profile) history.1
  rw [← Equiv.tsum_eq (informationHistoryEquiv runtime leaks initial initialized horizon scheduler
    who reference active valid)]
  exact tsum_congr fun history => informationHistoryEquiv_reachWeight runtime leaks initial
    initialized horizon scheduler profile who reference active valid history

/-- Bayes normalization transports exactly along the proved complete-fiber
bijection. Both antichain proofs come from the actual reactive information
models' complete private recall. -/
theorem bayesBelief_liftedInformationSite
    (profile : ∀ player, (RecoveryModel).BehavioralPolicy player)
    (positive : 0 < (NativeModel).informationMass
      (nativeProfile runtime leaks initial horizon scheduler profile) who NativeSite) :
    ((RecoveryModel).bayesBelief profile who RecoverySite
      ((runtime.recoveryApplication leaks).decisionInformationAntichain initial horizon scheduler
        who RecoverySite) (by
      rw [informationMass_liftedInformationSite runtime leaks initial initialized horizon scheduler
        who reference active valid decision profile]
      exact positive)).map
      (informationHistoryEquiv runtime leaks initial initialized horizon scheduler who reference
        active valid) =
      (NativeModel).bayesBelief
        (nativeProfile runtime leaks initial horizon scheduler profile) who NativeSite
        ((runtime.reactiveApplication leaks).decisionInformationAntichain
          (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
          who NativeSite) positive := by
  classical
  let equivalent := informationHistoryEquiv runtime leaks initial initialized horizon scheduler
    who reference active valid
  have mass := informationMass_liftedInformationSite runtime leaks initial initialized horizon
    scheduler who reference active valid decision profile
  have recoveryPositive : 0 < (RecoveryModel).informationMass profile who RecoverySite := by
    rw [mass]
    exact positive
  ext history
  obtain ⟨original, rfl⟩ := equivalent.surjective history
  rw [pmf_map_apply_of_injective _ equivalent.injective]
  calc
    _ = (RecoveryModel).historyReachWeight profile original.1 /
        (RecoveryModel).informationMass profile who RecoverySite :=
      (RecoveryModel).bayesBelief_apply profile who RecoverySite
        ((runtime.recoveryApplication leaks).decisionInformationAntichain initial horizon scheduler
          who RecoverySite) recoveryPositive original
    _ = (NativeModel).historyReachWeight
          (nativeProfile runtime leaks initial horizon scheduler profile) (equivalent original).1 /
        (NativeModel).informationMass
          (nativeProfile runtime leaks initial horizon scheduler profile) who NativeSite := by
      rw [mass, informationHistoryEquiv_reachWeight runtime leaks initial initialized horizon
        scheduler profile who reference active valid original]
    _ = _ := ((NativeModel).bayesBelief_apply
      (nativeProfile runtime leaks initial horizon scheduler profile) who NativeSite
      ((runtime.reactiveApplication leaks).decisionInformationAntichain
        (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
        who NativeSite) positive (equivalent original)).symm

end Vegas.EventGraphRuntime.RecoveryProjection
