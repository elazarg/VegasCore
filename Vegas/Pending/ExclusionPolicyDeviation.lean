/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedProfile
import Vegas.Pending.ExclusionInformationHistory
import GameTheory.Protocol.PolicyRandomization

/-! # Local policy deviations through the clear native projection -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (RecoveryState graph)) (horizon : Nat)
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeMenu" => MessageBounds.onePacketMenu runtime leaks bounds
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NativeModel" => ReactiveApplication.ResponseMenu.information
  (NativeMenu) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.ResponseMenu.information
  (RecoveryMenu) initial horizon scheduler

/-- Replacing one whole recovery policy commutes with its native projection. -/
theorem boundedNativeProfile_update
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (focal : Player) (alternative : (RecoveryModel).BehavioralPolicy focal) :
    boundedNativeProfile runtime leaks bounds initial horizon scheduler
      (Profile.update (sig := (RecoveryModel).behavioralSignature) profile focal alternative) =
      Profile.update (sig := (NativeModel).behavioralSignature)
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) focal
        (fun input => (alternative (liftInformation runtime leaks input)).map
          (boundedChoiceEquiv runtime leaks bounds initial horizon scheduler focal input)) := by
  funext who input
  by_cases same : who = focal
  · subst who
    simp only [boundedNativeProfile, Profile.update_same]
  · simp only [boundedNativeProfile, Profile.update_of_ne _ _ same]

/-- Replacing one recovery decision law commutes with the actual bounded
native projection at its complete clear input. All other native laws are kept. -/
theorem boundedNativeProfile_update_withLaw
    [∀ who, DecidableEq ((NativeModel).InfoState who)]
    [∀ who, DecidableEq ((RecoveryModel).InfoState who)]
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (focal : Player) (input : (runtime.reactiveApplication leaks).Info)
    (law : PMF ((RecoveryModel).Choice focal (liftInformation runtime leaks input))) :
    boundedNativeProfile runtime leaks bounds initial horizon scheduler
      (Profile.update (sig := (RecoveryModel).behavioralSignature) profile focal
        ((profile focal).withLaw (liftInformation runtime leaks input) law)) =
      Profile.update (sig := (NativeModel).behavioralSignature)
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile) focal
        ((boundedNativeProfile runtime leaks bounds initial horizon scheduler profile focal).withLaw
          input (law.map (boundedChoiceEquiv runtime leaks bounds initial horizon scheduler
            focal input))) := by
  funext who other
  by_cases playerEq : who = focal
  · subst who
    by_cases inputEq : other = input
    · subst other
      simp only [boundedNativeProfile, Profile.update_same, BehavioralPolicy.withLaw_self]
    · have liftedNe : liftInformation runtime leaks other ≠ liftInformation runtime leaks input :=
        fun equal => inputEq (by
          have projected := congrArg (information runtime leaks) equal
          simpa only [information_liftInformation] using projected)
      simp only [boundedNativeProfile, Profile.update_same,
        BehavioralPolicy.withLaw_of_ne (M := RecoveryModel) (profile focal)
          (liftInformation runtime leaks input) law liftedNe,
        BehavioralPolicy.withLaw_of_ne _ _ _ inputEq]
  · simp only [boundedNativeProfile, Profile.update_of_ne _ _ playerEq]

end Vegas.EventGraphRuntime.RecoveryProjection
