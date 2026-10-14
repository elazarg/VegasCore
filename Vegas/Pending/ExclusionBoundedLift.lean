/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedProfile
import Interaction.ReactiveFiniteAssessment

/-! # Lifting bounded operational laws into the recovery game

Native laws are retained at complete clear lifts. Other full inputs use the
actual recovery menu's uniform reference law.
-/

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

local notation "NativeMenu" => MessageBounds.onePacketMenu runtime leaks bounds
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NativeModel" => ReactiveApplication.ResponseMenu.information
  (NativeMenu) (PMF.map RecoveryState.native initial) horizon
  (nativeScheduler runtime leaks scheduler)
local notation "RecoveryModel" => ReactiveApplication.ResponseMenu.information
  (RecoveryMenu) initial horizon scheduler

/-- Complete recovery inputs with all the current and recalled exclusion flags
of a clear native lift. -/
def ClearInput (input : (runtime.recoveryApplication leaks).Info) : Prop :=
  liftInformation runtime leaks (information runtime leaks input) = input

omit [Fintype Player] in
@[simp]
theorem clearInput_lift (input : (runtime.reactiveApplication leaks).Info) :
    ClearInput runtime leaks (liftInformation runtime leaks input) := by
  unfold ClearInput
  rw [information_liftInformation]

/-- The inverse bounded-choice equivalence at a complete clear recovery input. -/
def boundedRecoveryChoiceEquiv (who : Player)
    (input : (runtime.recoveryApplication leaks).Info) (clear : ClearInput runtime leaks input) :
    (NativeModel).Choice who (information runtime leaks input) ≃
      (RecoveryModel).Choice who input :=
  (boundedChoiceEquiv runtime leaks bounds initial horizon scheduler who
    (information runtime leaks input)).symm.trans
      (Equiv.cast (congrArg (fun value => (RecoveryModel).Choice who value) clear))

open Classical in
/-- Lift a native bounded law at a complete clear input, and use the actual
recovery reference law elsewhere. -/
def boundedRecoveryLaw (who : Player) (input : (runtime.recoveryApplication leaks).Info)
    (law : PMF ((NativeModel).Choice who (information runtime leaks input))) :
    PMF ((RecoveryModel).Choice who input) :=
  if clear : ClearInput runtime leaks input then
    law.map (boundedRecoveryChoiceEquiv runtime leaks bounds initial horizon scheduler who input
      clear)
  else (RecoveryMenu).uniformPolicy initial horizon scheduler who input

/-- Lift all native finite-menu policies at their complete clear inputs. -/
def boundedRecoveryProfile (profile : ∀ who, (NativeModel).BehavioralPolicy who) :
    ∀ who, (RecoveryModel).BehavioralPolicy who := fun who input =>
  boundedRecoveryLaw runtime leaks bounds initial horizon scheduler who input
    (profile who (information runtime leaks input))

open Classical in
theorem boundedRecoveryLaw_fullSupport (who : Player)
    (input : (runtime.recoveryApplication leaks).Info)
    (law : PMF ((NativeModel).Choice who (information runtime leaks input)))
    (full : FullSupport law) :
    FullSupport (boundedRecoveryLaw runtime leaks bounds initial horizon scheduler who input law) :=
    by
  intro choice
  unfold boundedRecoveryLaw
  split
  · rename_i clear
    rw [PMF.mem_support_map_iff]
    let equivalent := boundedRecoveryChoiceEquiv runtime leaks bounds initial horizon scheduler
      who input clear
    exact ⟨equivalent.symm choice, full _, equivalent.apply_symm_apply choice⟩
  · let := Fintype.ofFinite ((RecoveryModel).Choice who input)
    exact PMF.mem_support_uniformOfFintype choice

/-- The lifted profile has full support at every full input if the original
profile does, including inputs that are not genuine recovery decisions. -/
theorem boundedRecoveryProfile_fullSupport
    (profile : ∀ who, (NativeModel).BehavioralPolicy who)
    (full : ∀ who input, FullSupport (profile who input)) :
    ∀ who input, FullSupport
      (boundedRecoveryProfile runtime leaks bounds initial horizon scheduler profile who input) :=
  fun who input => boundedRecoveryLaw_fullSupport runtime leaks bounds initial horizon scheduler
    who input _ (full who _)


private theorem cast_choice_val (who : Player)
    {first second : (runtime.recoveryApplication leaks).Info} (same : first = second)
    (choice : (RecoveryModel).Choice who first) :
    (Equiv.cast (congrArg (fun input => (RecoveryModel).Choice who input) same) choice).1 =
      choice.1 := by
  subst second
  rfl

/-- The clear inverse choice carries exactly the lifted optional native action. -/
theorem boundedRecoveryChoiceEquiv_val (who : Player)
    (input : (runtime.recoveryApplication leaks).Info) (clear : ClearInput runtime leaks input)
    (choice : (NativeModel).Choice who (information runtime leaks input)) :
    (boundedRecoveryChoiceEquiv runtime leaks bounds initial horizon scheduler who input clear
      choice).1 = choice.1.map (liftAction runtime leaks) := by
  unfold boundedRecoveryChoiceEquiv
  rw [Equiv.trans_apply, cast_choice_val runtime leaks bounds initial horizon scheduler who clear]
  rfl

/-- Projecting the actual optional action of the clear inverse recovers the
original source-menu choice. -/
theorem boundedRecoveryChoiceEquiv_projected_val (who : Player)
    (input : (runtime.recoveryApplication leaks).Info) (clear : ClearInput runtime leaks input)
    (choice : (NativeModel).Choice who (information runtime leaks input)) :
    (boundedRecoveryChoiceEquiv runtime leaks bounds initial horizon scheduler who input clear
      choice).1.map (action runtime leaks) = choice.1 := by
  rw [boundedRecoveryChoiceEquiv_val]
  cases choice.1 <;>
    simp only [Option.map_none, Option.map_some, action_liftAction]

open Classical in
/-- At complete clear inputs the lifted law preserves each actual optional
packet action, not just an abstract equivalence of choice carriers. -/
theorem boundedRecoveryLaw_map_val (who : Player)
    (input : (runtime.recoveryApplication leaks).Info) (clear : ClearInput runtime leaks input)
    (law : PMF ((NativeModel).Choice who (information runtime leaks input))) :
    (boundedRecoveryLaw runtime leaks bounds initial horizon scheduler who input law).map
        (fun choice => choice.1.map (action runtime leaks)) = law.map Subtype.val := by
  rw [boundedRecoveryLaw, dite_eq_left clear, PMF.map_comp]
  congr 1
  funext choice
  exact boundedRecoveryChoiceEquiv_projected_val runtime leaks bounds initial horizon scheduler
    who input clear choice

open Classical in
/-- The inverse choice relabeling recovers the native law exactly at every
complete clear recovery input. -/
theorem boundedRecoveryLaw_projected (who : Player)
    (input : (runtime.recoveryApplication leaks).Info) (clear : ClearInput runtime leaks input)
    (law : PMF ((NativeModel).Choice who (information runtime leaks input))) :
    (boundedRecoveryLaw runtime leaks bounds initial horizon scheduler who input law).map
        (boundedRecoveryChoiceEquiv runtime leaks bounds initial horizon scheduler who input
          clear).symm = law := by
  rw [boundedRecoveryLaw, dite_eq_left clear, PMF.map_comp]
  convert PMF.map_id law using 1
  congr 1
  funext choice
  exact (boundedRecoveryChoiceEquiv runtime leaks bounds initial horizon scheduler who input clear)
    |>.symm_apply_apply choice

omit [Fintype Player] in
/-- Every full input actually observed at a clear recovery prefix is a complete
clear lift, including all recalled private inputs and traffic. -/
theorem clearInput_of_history
    (history : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) (who : Player) :
    ClearInput runtime leaks
      (((runtime.recoveryApplication leaks).information initial horizon scheduler).infoOf who
        history.trace) := by
  simp only [ReactiveApplication.information, ReactiveApplication.info]
  cases state : history.state with
  | none => rfl
  | some current =>
      have restored : liftProtocolState runtime leaks
          (protocolState runtime leaks (some current)) = some current := by
        change some ⟨current.remaining, current.actor,
          liftExecution runtime leaks (execution runtime leaks current.execution)⟩ = some current
        rw [liftExecution_execution_of_history_clear runtime leaks initial horizon scheduler current
          (state ▸ history.trace) (clear current state)]
      unfold ClearInput
      rw [← observe_projection, ← observe_lift, restored]

end Vegas.EventGraphRuntime.RecoveryProjection
