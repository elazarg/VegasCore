/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionInformationHistory
import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Behavioral profiles evaluated at clear native information -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (RecoveryState graph)) (horizon : Nat)
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

local notation "NativeModel" => ReactiveApplication.information
  (reactiveApplication runtime leaks) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.information
  (recoveryApplication runtime leaks) initial horizon scheduler

/-- All raw choices at lifted information are the same optional transmissions. -/
def choiceEquiv (who : Player) (input : (runtime.reactiveApplication leaks).Info) :
    (RecoveryModel).Choice who (liftInformation runtime leaks input) ≃
      (NativeModel).Choice who input
    where
  toFun choice := ⟨choice.1.map (action runtime leaks), by
    change (choice.1.map (action runtime leaks)).isSome = input.isSome
    have permitted := choice.2
    change choice.1.isSome = (liftInformation runtime leaks input).isSome at permitted
    simpa only [Option.isSome_map, liftInformation] using permitted⟩
  invFun choice := ⟨choice.1.map (liftAction runtime leaks), by
    change (choice.1.map (liftAction runtime leaks)).isSome =
      (liftInformation runtime leaks input).isSome
    have permitted := choice.2
    change choice.1.isSome = input.isSome at permitted
    simpa only [Option.isSome_map, liftInformation] using permitted⟩
  left_inv choice := by
    apply Subtype.ext
    cases chosen : choice.1 <;>
      simp only [chosen, Option.map_none, Option.map_some, liftAction_action]
  right_inv choice := by
    apply Subtype.ext
    cases chosen : choice.1 <;>
      simp only [chosen, Option.map_none, Option.map_some, action_liftAction]

/-- Evaluate the recovery profile at complete clear lifts of native inputs,
then project its optional transmissions. -/
def nativeProfile (profile : ∀ who, (RecoveryModel).BehavioralPolicy who) :
    ∀ who, (NativeModel).BehavioralPolicy who := fun who input =>
  (profile who (liftInformation runtime leaks input)).map
    (choiceEquiv runtime leaks initial horizon scheduler who input)

theorem nativeProfile_map_val (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (who : Player) (input : (runtime.reactiveApplication leaks).Info) :
    ((nativeProfile runtime leaks initial horizon scheduler profile who input).map Subtype.val) =
      ((profile who (liftInformation runtime leaks input)).map Subtype.val).map
        (Option.map (action runtime leaks)) := by
  simp only [nativeProfile, PMF.map_comp, Function.comp_def]
  rfl

theorem projectedOption_injective : Function.Injective (Option.map (action runtime leaks)) := by
  apply Function.LeftInverse.injective
    (g := Option.map (liftAction runtime leaks))
  intro option
  cases option <;> simp only [Option.map_none, Option.map_some, liftAction_action]

/-- Exact native action probabilities, stated on bare options so transporting
an information input never requires transporting a dependent menu subtype. -/
theorem nativeProfile_option_apply
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who)
    (who : Player) (input : (runtime.reactiveApplication leaks).Info)
    (option : Option (runtime.reactiveApplication leaks).Action) :
    ((nativeProfile runtime leaks initial horizon scheduler profile who input).map Subtype.val)
        option =
      ((profile who (liftInformation runtime leaks input)).map Subtype.val)
        (option.map (liftAction runtime leaks)) := by
  rw [nativeProfile_map_val]
  have mass := pmf_map_apply_of_injective
    ((profile who (liftInformation runtime leaks input)).map Subtype.val)
    (projectedOption_injective runtime leaks) (option.map (liftAction runtime leaks))
  have back : (option.map (liftAction runtime leaks)).map (action runtime leaks) = option := by
    cases option <;> simp only [Option.map_none, Option.map_some, action_liftAction]
  rw [back] at mass
  exact mass

end Vegas.EventGraphRuntime.RecoveryProjection
