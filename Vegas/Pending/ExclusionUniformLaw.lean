/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedLift
import GameTheory.Math.Probability.Support

/-! # Uniform bounded laws at clear recovery inputs

The existing bounded-choice equivalence preserves the uniform reference law.
This identifies the reference tremble before permanent public exclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Math.Probability

private theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (equivalent : α ≃ β) :
    (PMF.uniformOfFintype α).map equivalent = PMF.uniformOfFintype β := by
  classical
  ext target
  obtain ⟨source, rfl⟩ := equivalent.surjective target
  rw [pmf_map_apply_of_injective _ equivalent.injective]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr equivalent]

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (RecoveryState graph)) (horizon : Nat)
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeMenu" => MessageBounds.onePacketMenu runtime leaks bounds
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NativeModel" => ReactiveApplication.ResponseMenu.information
  (MessageBounds.onePacketMenu runtime leaks bounds) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.ResponseMenu.information
  (Recovery.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- The recovery uniform bounded law projects to the native uniform bounded law
at every complete clear input. -/
theorem uniformPolicy_projected (who : Player)
    (input : (runtime.recoveryApplication leaks).Info) (clear : ClearInput runtime leaks input) :
    ((RecoveryMenu).uniformPolicy initial horizon scheduler who input).map
        (boundedRecoveryChoiceEquiv runtime leaks bounds initial horizon scheduler who input
          clear).symm =
      (NativeMenu).uniformPolicy (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) who (information runtime leaks input) := by
  let := Fintype.ofFinite ((RecoveryModel).Choice who input)
  let := Fintype.ofFinite ((NativeModel).Choice who (information runtime leaks input))
  change (PMF.uniformOfFintype _).map
    (boundedRecoveryChoiceEquiv runtime leaks bounds initial horizon scheduler who input
      clear).symm = PMF.uniformOfFintype _
  exact uniform_map_equiv _

/-- At a canonical clear lift the bounded native choice map preserves the
uniform reference law exactly. -/
theorem uniformPolicy_liftedInformation (who : Player)
    (input : (runtime.reactiveApplication leaks).Info) :
    ((RecoveryMenu).uniformPolicy initial horizon scheduler who
      (liftInformation runtime leaks input)).map
        (boundedChoiceEquiv runtime leaks bounds initial horizon scheduler who input) =
      (NativeMenu).uniformPolicy (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) who input := by
  let := Fintype.ofFinite ((RecoveryModel).Choice who (liftInformation runtime leaks input))
  let := Fintype.ofFinite ((NativeModel).Choice who input)
  change (PMF.uniformOfFintype _).map
    (boundedChoiceEquiv runtime leaks bounds initial horizon scheduler who input) =
      PMF.uniformOfFintype _
  exact uniform_map_equiv _

end Vegas.EventGraphRuntime.RecoveryProjection
