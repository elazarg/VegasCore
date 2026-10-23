/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionNativeProfile
import Vegas.Pending.ExclusionMenuProjection
import Interaction.ReactiveResponseEmbedding

/-! # Bounded one-packet profiles at clear native information -/

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

/-- Bounded action menus agree at complete clear lifts of native inputs. -/
theorem onePacket_actions_lifted (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.recoveryApplication leaks).Action) :
    response ∈ (RecoveryMenu).actions who (past.map (liftPlayerEntry runtime leaks))
        (liftPlayerView runtime leaks view) ↔
      action runtime leaks response ∈ (NativeMenu).actions who past view := by
  simpa only [List.map_map, Function.comp_def, playerEntry_liftPlayerEntry,
    playerView_liftPlayerView, List.map_id_fun', id_eq] using
    Recovery.onePacketMenu_projected_of_empty runtime leaks bounds who
      (past.map (liftPlayerEntry runtime leaks)) (liftPlayerView runtime leaks view) rfl response

/-- Menu membership of optional transmissions is preserved and reflected at
every clear lifted input, whether or not that input is reached. -/
theorem onePacket_option_projected (who : Player)
    (input : (runtime.reactiveApplication leaks).Info)
    (option : Option (runtime.recoveryApplication leaks).Action) :
    option ∈ (RecoveryModel).menu who (liftInformation runtime leaks input) ↔
      option.map (action runtime leaks) ∈ (NativeModel).menu who input := by
  cases input with
  | none =>
    change option = none ↔ option.map (action runtime leaks) = none
    simp only [Option.map_eq_none_iff]
  | some input =>
    rcases input with ⟨past, view⟩
    change (∃ response ∈ (RecoveryMenu).actions who
        (past.map (liftPlayerEntry runtime leaks)) (liftPlayerView runtime leaks view),
          option = some response) ↔
      ∃ response ∈ (NativeMenu).actions who past view,
        option.map (action runtime leaks) = some response
    constructor
    · rintro ⟨response, permitted, same⟩
      refine ⟨action runtime leaks response,
        (onePacket_actions_lifted runtime leaks bounds who past view response).mp permitted, ?_⟩
      rw [same]
      rfl
    · rintro ⟨response, permitted, same⟩
      refine ⟨liftAction runtime leaks response, ?_, ?_⟩
      · apply (onePacket_actions_lifted runtime leaks bounds who past view _).mpr
        simpa only [action_liftAction] using permitted
      · apply projectedOption_injective runtime leaks
        simpa only [Option.map_some, action_liftAction] using same

/-- The finite one-packet choice carriers agree at all clear native inputs. -/
def boundedChoiceEquiv (who : Player) (input : (runtime.reactiveApplication leaks).Info) :
    (RecoveryModel).Choice who (liftInformation runtime leaks input) ≃
      (NativeModel).Choice who input where
  toFun choice := ⟨choice.1.map (action runtime leaks),
    (onePacket_option_projected runtime leaks bounds initial horizon scheduler who input _).mp
      choice.2⟩
  invFun choice := ⟨choice.1.map (liftAction runtime leaks), by
    apply (onePacket_option_projected runtime leaks bounds initial horizon scheduler
      who input _).mpr
    have projected : (choice.1.map (liftAction runtime leaks)).map (action runtime leaks) =
        choice.1 := by
      cases option : choice.1 <;>
        simp only [Option.map_none, Option.map_some, action_liftAction]
    rw [projected]
    exact choice.2⟩
  left_inv choice := by
    apply Subtype.ext
    cases option : choice.1 <;>
      simp only [option, Option.map_none, Option.map_some, liftAction_action]
  right_inv choice := by
    apply Subtype.ext
    cases option : choice.1 <;>
      simp only [option, Option.map_none, Option.map_some, action_liftAction]

/-- Project actual bounded recovery laws after evaluating them at complete
clear lifts of native full information. -/
def boundedNativeProfile (profile : ∀ who, (RecoveryModel).BehavioralPolicy who) :
    ∀ who, (NativeModel).BehavioralPolicy who := fun who input =>
  (profile who (liftInformation runtime leaks input)).map
    (boundedChoiceEquiv runtime leaks bounds initial horizon scheduler who input)

/-- Projecting the bounded profile and embedding it into the raw native game
is exactly the checked raw native profile of the embedded recovery profile. -/
theorem boundedNativeProfile_embed
    (profile : ∀ who, (RecoveryModel).BehavioralPolicy who) (who : Player) :
    (NativeMenu).embedPolicy (initial.map RecoveryState.native) horizon
        (nativeScheduler runtime leaks scheduler) who
        (boundedNativeProfile runtime leaks bounds initial horizon scheduler profile who) =
      nativeProfile runtime leaks initial horizon scheduler
        (fun player => (RecoveryMenu).embedPolicy initial horizon scheduler player (profile player))
        who := by
  funext input
  simp only [ReactiveApplication.ResponseMenu.embedPolicy, boundedNativeProfile, nativeProfile,
    PMF.map_comp, Function.comp_def]
  congr 1

end Vegas.EventGraphRuntime.RecoveryProjection
