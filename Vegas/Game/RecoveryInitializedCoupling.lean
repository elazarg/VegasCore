/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativePrior
import Vegas.Pending.ExclusionTerminalClearance

/-! # Initialized coupling of arbitrary finite recovery policies -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

private theorem initialized_state_law_prior_eq
    {Player : Type} [DecidableEq Player] [Fintype Player]
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    {first second : PMF app.State} (same : first = second) (horizon : Nat)
    (scheduler : app.Scheduler)
    (profile : ∀ who, (menu.information first horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) {Outcome : Type} (readout : app.ProtocolState → Outcome) :
    ((menu.information first horizon scheduler).runBehavioral profile fuel).map
        (fun final => readout final.state) =
      ((menu.information second horizon scheduler).runBehavioral
        (fun who input => (profile who input).map (Equiv.cast (congrArg
          (fun initial => (menu.information initial horizon scheduler).Choice who input) same)))
        fuel).map (fun final => readout final.state) := by
  subst second
  simp only [Equiv.cast_refl, Equiv.coe_refl, PMF.map_id]

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "RawN" => ReactiveApplication.information (application setup runtime leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)
local notation "RawR" => ReactiveApplication.information
  (recoveryApplication runtime leaks) Initial horizon scheduler
local notation "RawNP" => ReactiveApplication.protocol (application setup runtime leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)
local notation "RawRP" => ReactiveApplication.protocol
  (recoveryApplication runtime leaks) Initial horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

/-- Embedding the actual recovery policy, projecting it, and changing the prior
retain every initialized finite-menu native state law exactly. -/
theorem sourceNativeProfile_initialized_state_law
    (profile : ∀ who, (R).BehavioralPolicy who) (fuel : Nat)
    {Outcome : Type} (readout : (application setup runtime leaks).ProtocolState → Outcome) :
    ((RawN).runBehavioral
      (nativeProfile runtime leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who))) fuel).map
        (fun final => readout final.state) =
      ((N).runBehavioral (sourceNativeProfile setup runtime leaks bounds horizon scheduler profile)
        fuel).map (fun final => readout final.state) := by
  let genericInitial := PMF.map RecoveryState.native Initial
  let genericProfile := boundedNativeProfile runtime leaks bounds Initial horizon scheduler
    profile
  have rawLaw := (NMenu).run_embed genericInitial horizon (NativeScheduler) genericProfile fuel
    ((NMenu).protocol genericInitial horizon (NativeScheduler)).initHistory
  have profiles : (fun who => (NMenu).embedPolicy genericInitial horizon (NativeScheduler) who
      (genericProfile who)) =
      nativeProfile runtime leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)) := by
    funext who
    exact boundedNativeProfile_embed runtime leaks bounds Initial horizon scheduler
      profile who
  rw [profiles] at rawLaw
  have rawRead := congrArg (fun law : PMF (RawNP).History =>
    law.map (fun final => readout final.state)) rawLaw
  rw [PMF.map_comp] at rawRead
  have prior := initialized_state_law_prior_eq (NMenu) (initialLaw_native setup) horizon
    (NativeScheduler) genericProfile fuel readout
  have profileCast : (fun who input => (genericProfile who input).map (Equiv.cast (congrArg
      (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
        ((NMenu).information initial horizon (NativeScheduler)).Choice who input)
          (initialLaw_native setup)))) =
      sourceNativeProfile setup runtime leaks bounds horizon scheduler profile := by
    funext who input
    exact (sourceNativeProfile_eq_cast setup runtime leaks bounds horizon scheduler profile who
      input).symm
  have replaced := congrArg (fun players : ∀ who, (N).BehavioralPolicy who =>
    ((N).runBehavioral players fuel).map (fun final => readout final.state)) profileCast
  exact rawRead.symm.trans (prior.trans replaced)

/-- Raw projection and canonical finite native play retain the same terminal
public-failure mass at every finite horizon. -/
theorem sourceNativeProfile_initialized_failure_mass_eq
    (profile : ∀ who, (R).BehavioralPolicy who) (fuel : Nat) :
    (((RawN).runBehavioral
      (nativeProfile runtime leaks Initial horizon scheduler
        (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who)))
        fuel).toOuterMeasure
         {next | ¬ NativeClear runtime leaks Initial horizon scheduler next}).toReal =
      (((N).runBehavioral (sourceNativeProfile setup runtime leaks bounds horizon scheduler profile)
        fuel).toOuterMeasure {next | ¬ Clear next.state}).toReal := by
  classical
  let projected := nativeProfile runtime leaks Initial horizon scheduler
    (fun who => (RMenu).embedPolicy Initial horizon scheduler who (profile who))
  have states := sourceNativeProfile_initialized_state_law setup runtime leaks bounds horizon
    scheduler
    profile fuel id
  have failureEq :
      (((RawN).runBehavioral projected fuel).toOuterMeasure
        {next | ¬ NativeClear runtime leaks Initial horizon scheduler next}).toReal =
      (((N).runBehavioral (sourceNativeProfile setup runtime leaks bounds horizon scheduler profile)
        fuel).toOuterMeasure {next | ¬ Clear next.state}).toReal := by
    have same : {next : (RawNP).History |
        ¬ NativeClear runtime leaks Initial horizon scheduler next} =
        History.state ⁻¹' {state | ¬ Clear state} := by
      ext next
      exact not_congr (nativeClear_iff_stateInvariant runtime leaks Initial horizon
        scheduler next)
    rw [same, ← PMF.toOuterMeasure_map_apply]
    change (PMF.toOuterMeasure
      (((RawN).runBehavioral projected fuel).map (fun final => id final.state))
        {state | ¬ Clear state}).toReal = _
    rw [states, PMF.toOuterMeasure_map_apply]
    rfl
  exact failureEq

/-- The actual initialized finite recovery and native-projection joint laws
are close by exactly the native projection's terminal public-failure mass. -/
theorem recovery_initialized_projection_withinTV
    (profile : ∀ who, (R).BehavioralPolicy who)
    {Outcome : Type} (nativeRead : (application setup runtime leaks).ProtocolState → Outcome)
    (recoveryRead : (recoveryApplication runtime leaks).ProtocolState → Outcome)
    (agree : ∀ state, (∀ current, state = some current →
      current.execution.application.excluded = ∅) →
      recoveryRead state = nativeRead (protocolState runtime leaks state)) :
    PMF.WithinTV
      ((((N).runBehavioral (sourceNativeProfile setup runtime leaks bounds horizon scheduler
        profile)
        (2 * horizon + 1)).toOuterMeasure {next | ¬ Clear next.state}).toReal)
      (((R).runBehavioral profile (2 * horizon + 1)).map (fun final => recoveryRead final.state))
      (((N).runBehavioral (sourceNativeProfile setup runtime leaks bounds horizon scheduler profile)
        (2 * horizon + 1)).map (fun final => nativeRead final.state)) := by
  have close := responseMenu_initialized_readout_withinTV_of_native_failure runtime leaks
    Initial horizon scheduler (initialLaw_initialized setup) (RMenu) profile nativeRead recoveryRead
      agree
  rw [sourceNativeProfile_initialized_failure_mass_eq setup runtime leaks bounds horizon scheduler
    profile
    (2 * horizon + 1),
    sourceNativeProfile_initialized_state_law setup runtime leaks bounds horizon scheduler
      profile (2 * horizon + 1) nativeRead] at close
  exact close


end Vegas.RecoveryOnePacket
