/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedProfile
import Vegas.Pending.ExclusionClearBelief
import Interaction.ReactiveResponseBelief
import Interaction.ReactiveResponseDecision

/-! # One-packet beliefs before public exclusion

Finite-menu embedding and the complete clear-history bijection preserve the
entire information event and its normalized belief, including zero-reach fibers.
No comparison of continuations after exclusion is asserted.
-/

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
/-- Finite one-packet information events have equal actual probability before
public exclusion under the concretely projected bounded profile. -/
theorem bounded_informationMass_liftedInformationSite
    (profile : ∀ player, (RecoveryModel).BehavioralPolicy player) :
    (RecoveryModel).informationMass profile who RecoverySite =
      (NativeModel).informationMass
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who
        NativeSite := by
  let embedded := fun player =>
    (RecoveryMenu).embedPolicy initial horizon scheduler player (profile player)
  have projected : (fun player => (NativeMenu).embedPolicy
      (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler) player
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile player)) =
      nativeProfile runtime leaks initial horizon scheduler embedded := by
    funext player
    exact boundedNativeProfile_embed runtime leaks bounds initial horizon scheduler profile player
  calc
    _ = (RecoveryRaw).informationMass embedded who
        ((RecoveryMenu).rawSite initial horizon scheduler who RecoverySite) :=
      (RecoveryMenu).informationMass_rawSite initial horizon scheduler profile who RecoverySite
    _ = (NativeRaw).informationMass
          (fun player => (NativeMenu).embedPolicy
            (initial.map RecoveryState.native) horizon
            (nativeScheduler runtime leaks scheduler) player
            (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile player))
          who ((NativeMenu).rawSite (initial.map RecoveryState.native) horizon
            (nativeScheduler runtime leaks scheduler) who NativeSite) := by
      rw [projected]
      exact informationMass_liftedInformationSite runtime leaks initial initialized horizon
        scheduler who reference active valid
        ((NativeMenu).rawSite (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) who NativeSite).2 embedded
    _ = _ := ((NativeMenu).informationMass_rawSite (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler)
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who
      NativeSite).symm

include initialized active valid in
/-- A positive native one-packet information event supplies an actual recovery
one-packet decision at its complete clear lifted input. -/
def boundedLiftedInformationSite
    (profile : ∀ player, (RecoveryModel).BehavioralPolicy player)
    (positive : 0 < (NativeModel).informationMass
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who
      NativeSite) : (RecoveryModel).InformationSite who := by
  let embedded := fun player =>
    (RecoveryMenu).embedPolicy initial horizon scheduler player (profile player)
  let projected := boundedNativeProfile runtime leaks bounds initial horizon scheduler profile
  let rawNative := (NativeMenu).rawSite (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler) who NativeSite
  let rawRecovery := liftedInformationSite runtime leaks initial initialized horizon scheduler
    who reference active valid rawNative.2
  have profiles : (fun player => (NativeMenu).embedPolicy
      (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler) player
      (projected player)) = nativeProfile runtime leaks initial horizon scheduler embedded := by
    funext player
    exact boundedNativeProfile_embed runtime leaks bounds initial horizon scheduler profile player
  have nativeMass := (NativeMenu).informationMass_rawSite
    (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
    projected who NativeSite
  have rawPositive : 0 < (NativeRaw).informationMass
      (nativeProfile runtime leaks initial horizon scheduler embedded) who rawNative := by
    rw [← profiles, ← nativeMass]
    exact positive
  have recoveryPositive : 0 < (RecoveryRaw).informationMass embedded who rawRecovery := by
    rw [informationMass_liftedInformationSite runtime leaks initial initialized horizon scheduler
      who reference active valid rawNative.2 embedded]
    exact rawPositive
  exact ⟨liftInformation runtime leaks
      ((runtime.reactiveApplication leaks).observe who (some reference)),
    (RecoveryMenu).isDecisionInfo_of_raw_mass_pos initial horizon scheduler profile who
      rawRecovery recoveryPositive⟩

/-- The finite recovery belief, mapped through its raw embedding and the exact
clear-history equivalence, is the raw image of the finite native belief. -/
theorem bounded_bayesBelief_liftedInformationSite
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
      (fun history => informationHistoryEquiv runtime leaks initial initialized horizon scheduler
        who reference active valid
        ((RecoveryMenu).rawInformationHistory initial horizon scheduler who RecoverySite history)) =
      ((NativeModel).bayesBelief
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who NativeSite
        ((NativeMenu).decisionInformationAntichain (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) who NativeSite) positive).map
        ((NativeMenu).rawInformationHistory (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) who NativeSite) := by
  let embedded := fun player =>
    (RecoveryMenu).embedPolicy initial horizon scheduler player (profile player)
  let projected := boundedNativeProfile runtime leaks bounds initial horizon scheduler profile
  let equivalent := informationHistoryEquiv runtime leaks initial initialized horizon scheduler
    who reference active valid
  have profiles : (fun player => (NativeMenu).embedPolicy
      (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler) player
      (projected player)) = nativeProfile runtime leaks initial horizon scheduler embedded := by
    funext player
    exact boundedNativeProfile_embed runtime leaks bounds initial horizon scheduler profile player
  have recoveryPositive : 0 < (RecoveryModel).informationMass profile who RecoverySite := by
    rw [bounded_informationMass_liftedInformationSite runtime leaks bounds initial initialized
      horizon scheduler who reference active valid nativeDecision recoveryDecision profile]
    exact positive
  have nativeMass := (NativeMenu).informationMass_rawSite
    (initial.map RecoveryState.native) horizon (nativeScheduler runtime leaks scheduler)
    projected who NativeSite
  have nativePositive : 0 < (NativeRaw).informationMass
      (nativeProfile runtime leaks initial horizon scheduler embedded) who
      ((NativeMenu).rawSite (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) who NativeSite) := by
    rw [← profiles, ← nativeMass]
    exact positive
  have recoveryEmbed := (RecoveryMenu).bayesBelief_rawSite initial horizon scheduler profile who
    RecoverySite recoveryPositive
  have transported := bayesBelief_liftedInformationSite runtime leaks initial initialized horizon
    scheduler who reference active valid
    ((NativeMenu).rawSite (initial.map RecoveryState.native) horizon
      (nativeScheduler runtime leaks scheduler) who NativeSite).2 embedded nativePositive
  have nativeEmbed := (NativeMenu).bayesBelief_rawSite (initial.map RecoveryState.native) horizon
    (nativeScheduler runtime leaks scheduler) projected who NativeSite positive
  have mapped := congrArg (fun law => law.map equivalent) recoveryEmbed
  rw [PMF.map_comp] at mapped
  calc
    _ = _ := mapped
    _ = _ := transported
    _ = _ := by
      refine Eq.trans ?_ nativeEmbed.symm
      congr 1
      exact profiles.symm

/-- Exact finite-menu Bayes transport at the recovery site derived from the
positive native information event; no recovery decision-validity premise is needed. -/
theorem bounded_bayesBelief_liftedSite
    (profile : ∀ player, (RecoveryModel).BehavioralPolicy player)
    (positive : 0 < (NativeModel).informationMass
      (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who
      NativeSite) :
    let site := boundedLiftedInformationSite runtime leaks bounds initial initialized horizon
      scheduler who reference active valid nativeDecision profile positive
    ((RecoveryModel).bayesBelief profile who site
      ((RecoveryMenu).decisionInformationAntichain initial horizon scheduler who site)
      (by
        change 0 < (RecoveryModel).informationMass profile who
          ⟨liftInformation runtime leaks
            ((runtime.reactiveApplication leaks).observe who (some reference)), site.2⟩
        rw [bounded_informationMass_liftedInformationSite runtime leaks bounds initial initialized
          horizon scheduler who reference active valid nativeDecision site.2 profile]
        exact positive)).map
      (fun history => informationHistoryEquiv runtime leaks initial initialized horizon scheduler
        who reference active valid
        ((RecoveryMenu).rawInformationHistory initial horizon scheduler who site history)) =
      ((NativeModel).bayesBelief
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) who NativeSite
        ((NativeMenu).decisionInformationAntichain (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) who NativeSite) positive).map
        ((NativeMenu).rawInformationHistory (initial.map RecoveryState.native) horizon
          (nativeScheduler runtime leaks scheduler) who NativeSite) := by
  exact bounded_bayesBelief_liftedInformationSite runtime leaks bounds initial initialized horizon
    scheduler who reference active valid nativeDecision
    (boundedLiftedInformationSite runtime leaks bounds initial initialized horizon scheduler who
      reference active valid nativeDecision profile positive).2 profile positive

end Vegas.EventGraphRuntime.RecoveryProjection
