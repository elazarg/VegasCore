/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedLift

/-! # Exact round trip of bounded native profiles through clear recovery laws -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (RecoveryState graph)) (horizon : Nat)
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeModel" => ReactiveApplication.ResponseMenu.information
  (MessageBounds.onePacketMenu runtime leaks bounds) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)

/-- Native projection recovers every input law of the inverse-lifted bounded
profile, including native inputs that are not actual recovery decisions. -/
theorem boundedNativeProfile_boundedRecoveryProfile
    (profile : ∀ who, (NativeModel).BehavioralPolicy who) :
    boundedNativeProfile runtime leaks bounds initial horizon scheduler
      (boundedRecoveryProfile runtime leaks bounds initial horizon scheduler profile) =
      profile := by
  funext who input
  apply pmf_map_injective Subtype.val_injective
  have lifted := boundedRecoveryLaw_map_val runtime leaks bounds initial horizon scheduler who
    (liftInformation runtime leaks input) (clearInput_lift runtime leaks input)
    (profile who (information runtime leaks (liftInformation runtime leaks input)))
  calc
    _ = _ := by
      rw [boundedNativeProfile, PMF.map_comp]
      rfl
    _ = _ := lifted
    _ = _ := congrArg (fun value => (profile who value).map Subtype.val)
      (information_liftInformation runtime leaks input)

end Vegas.EventGraphRuntime.RecoveryProjection
