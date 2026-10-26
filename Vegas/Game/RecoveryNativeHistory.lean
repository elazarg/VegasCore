/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativePrior
import Vegas.Pending.ExclusionBoundedHistory
import GameTheory.Protocol.PolicyRandomization

/-! # Genuine bounded native histories from clear recovery histories

The canonical finite projection retains the full realized native history and
physical control state. Whole focal policy updates commute with the actual
native policy encoding. No service or payoff contract is involved.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

private theorem history_cast_raw {Player : Type} [DecidableEq Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler) (history : (menu.protocol first horizon scheduler).History) :
    menu.toRawHistory second horizon scheduler
        (Equiv.cast (congrArg (fun initial => (menu.protocol initial horizon scheduler).History)
          same) history) =
      Equiv.cast (congrArg (fun initial => (app.protocol initial horizon scheduler).History) same)
        (menu.toRawHistory first horizon scheduler history) := by
  subst second
  rfl

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "RApp" => recoveryApplication runtime leaks
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (MessageBounds.onePacketMenu runtime leaks bounds) (initialLaw setup) horizon
  (NativeScheduler)

/-- The genuine finite native projection of any entire actual clear recovery
history at the canonical source prior. -/
def nativeClearHistory (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) : (NP).History :=
  Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).protocol initial horizon (NativeScheduler)).History) (initialLaw_native setup))
    (exists_nativeBoundedHistory runtime leaks bounds Initial
      (initialLaw_initialized setup) horizon scheduler history clear).choose

/-- The finite projection retains the exact realized projected raw history. -/
theorem nativeClearHistory_raw (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler)
        (nativeClearHistory setup runtime leaks bounds horizon scheduler history clear) =
      Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((application setup runtime leaks).protocol initial horizon (NativeScheduler)).History)
          (initialLaw_native setup))
        (nativeHistory runtime leaks Initial horizon scheduler
          ((RMenu).toRawHistory Initial horizon scheduler history) clear) := by
  unfold nativeClearHistory
  rw [history_cast_raw (NMenu) (initialLaw_native setup) horizon (NativeScheduler)]
  exact congrArg _ (exists_nativeBoundedHistory runtime leaks bounds Initial
    (initialLaw_initialized setup) horizon scheduler history clear).choose_spec


/-- Exact raw projection uniquely identifies the finite native start used by
the continuation estimate, regardless of the projection's chosen witnesses. -/
theorem nativeClearHistory_eq_of_raw (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅)
    (native : (NP).History)
    (same : (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) native =
      Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((application setup runtime leaks).protocol initial horizon (NativeScheduler)).History)
          (initialLaw_native setup))
        (nativeHistory runtime leaks Initial horizon scheduler
          ((RMenu).toRawHistory Initial horizon scheduler history) clear)) :
    nativeClearHistory setup runtime leaks bounds horizon scheduler history clear = native :=
  (NMenu).toRawHistory_injective (initialLaw setup) horizon (NativeScheduler)
    ((nativeClearHistory_raw setup runtime leaks bounds horizon scheduler history clear).trans
      same.symm)

/-- Replacing a whole actual recovery policy commutes with canonical projection. -/
theorem sourceNativeProfile_update
    (profile : ∀ who, (R).BehavioralPolicy who)
    (focal : Player) (alternative : (R).BehavioralPolicy focal) :
    sourceNativeProfile setup runtime leaks bounds horizon scheduler
      (Profile.update (sig := (R).behavioralSignature) profile focal alternative) =
      Profile.update (sig := (N).behavioralSignature)
        (sourceNativeProfile setup runtime leaks bounds horizon scheduler profile) focal
        (fun input => (alternative (liftInformation runtime leaks input)).map
          (sourceNativeChoiceEquiv setup runtime leaks bounds horizon scheduler focal input)) := by
  funext who input
  by_cases same : who = focal
  · subst who
    simp only [sourceNativeProfile, Profile.update_same]
  · simp only [sourceNativeProfile, Profile.update_of_ne _ _ same]

/-- Canonical finite projection preserves the complete projected control state. -/
theorem nativeClearHistory_state (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅) :
    (nativeClearHistory setup runtime leaks bounds horizon scheduler history clear).state =
      protocolState runtime leaks history.state := by
  have raw := nativeClearHistory_raw setup runtime leaks bounds horizon scheduler history clear
  have states := congrArg History.state raw
  have castState {first second : PMF (EventGraphRuntime.State (graph setup))}
      (same : first = second)
      (found : ((application setup runtime leaks).protocol first horizon
        (NativeScheduler)).History) :
      (Equiv.cast (congrArg (fun initial =>
        ((application setup runtime leaks).protocol initial horizon (NativeScheduler)).History)
          same) found).state = found.state := by
    subst second
    rfl
  exact states.trans (castState (initialLaw_native setup) _)

/-- The physical own turn is fixed throughout an actual observed decision fiber. -/
theorem informationHistory_control_turn {who : Player}
    {past : List (recoveryApplication runtime leaks).PlayerEntry}
    {view : (recoveryApplication runtime leaks).PlayerView}
    (history : (R).InformationHistory who (some (past, view)))
    {event : (graph setup).EventId}
    (turn : view.application.1.publicView.ownTurn? who = some event) :
    ∃ current : (recoveryApplication runtime leaks).Control,
      history.1.state = some current ∧
        current.execution.application.native.publicView.ownTurn? who = some event := by
  have observed := ((RMenu).info Initial horizon scheduler who history.1.trace).symm.trans history.2
  cases state : history.1.state with
  | none => rw [state] at observed; cases observed
  | some current =>
    rw [state] at observed
    by_cases active : current.actor = some who
    · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
      have viewEq : current.execution.observe (RApp) who = view :=
        congrArg Prod.snd (Option.some.inj observed)
      refine ⟨current, rfl, ?_⟩
      exact (congrArg (fun observed : (RApp).PlayerView =>
        observed.application.1.publicView.ownTurn? who) viewEq).trans turn
    · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
      cases observed

end Vegas.RecoveryOnePacket
