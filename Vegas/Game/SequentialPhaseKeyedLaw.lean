/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonMixture
import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.RecoveryNativeLaw

/-! # Keyed local laws under the concrete phase-to-native choice maps -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "Initial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (oldLeaks)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) Initial horizon
  (oldScheduler)
local notation "NP" => onePacketProtocol setup (oldLeaks) bounds horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup (oldLeaks))
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application setup (oldLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local instance keyedLawComparisonHistory : Fintype ((RMenu).protocol
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).History :=
  sourceHistoryFintype setup leaks bounds horizon scheduler

local instance keyedLawComparisonInformation (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds
      ((Vegas.initialLaw setup).map (fun native =>
        (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).InfoState who) :=
  sourceInfoDecidableEq setup leaks bounds horizon scheduler who

local instance keyedLawComparisonNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance keyedLawNativeInformation (who : Player) : DecidableEq ((N).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

local instance keyedLawRecoveryNature :
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) (oldScheduler) :=
  recoveryNature setup leaks scheduler

local instance keyedLawNativeHistory : Fintype (NP).History :=
  @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (NMenu) (Vegas.initialLaw setup)
    horizon (NativeScheduler) inferInstance (nativeNature setup leaks scheduler)

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

open Classical in
/-- A keyed phase decision has an actual current owner turn and an actual shared key. -/
theorem keyed_information {who : Player} (site : (M).InformationSite who)
    (keyed : KeyedAgent setup leaks bounds horizon scheduler ((M).agentAt site)) :
    ∃ (past : List (P).PlayerEntry) (view : (P).PlayerView)
      (event : (graph setup).EventId) (key : LateKey setup (oldLeaks)),
      site.1 = some (past, view) ∧
      view.application.1.publicView.ownTurn? who = some event ∧
      agentKey setup leaks bounds horizon scheduler ((M).agentAt site) = some key := by
  obtain ⟨nativePast, nativeView, event, atNative, pending, _activated⟩ := keyed
  have found : ∃ input, site.1 = some input := by
    cases current : site.1 with
    | none => simp [PhaseRecoveryProjection.information, RecoveryProjection.information,
        current] at atNative
    | some input => exact ⟨input, rfl⟩
  obtain ⟨⟨past, view⟩, atSite⟩ := found
  have nativePending := pending
  rw [atNative] at nativePending
  have turn := (pendingEvent_spec (setup := setup) nativePending).1
  have nativePair := atNative
  rw [atSite] at nativePair
  simp only [PhaseRecoveryProjection.information, RecoveryProjection.information, Option.map_some]
    at nativePair
  have views := congrArg Prod.snd (Option.some.inj nativePair)
  change RecoveryProjection.playerView (runtime setup) (oldLeaks)
    (PhaseRecoveryProjection.playerView (runtime setup) leaks (oldLeaks) view) = nativeView at views
  rw [← views] at turn
  refine ⟨past, view, event, LateKey.ofView setup (oldLeaks) who nativePast nativeView, atSite,
    turn, ?_⟩
  change lateKey setup (oldLeaks) who
    (RecoveryProjection.information (runtime setup) (oldLeaks) (projectInfo site.1)) = _
  rw [atNative]
  rfl

open Classical in
/-- The actual keyed phase law maps to exactly the same native late option,
including all menu casts forced by the fixed comparison information fiber. -/
theorem keyedComponent_native_choice
    (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {who : Player} (site : (M).InformationSite who)
    (clear : ClearInput setup leaks site.1) (nativeSite : (N).InformationSite who)
    (lifted : RecoveryProjection.liftInformation (runtime setup) (oldLeaks) nativeSite.1 =
      projectInfo site.1) (option : LateOption slots) :
    (((keyedComponent setup leaks bounds horizon scheduler source scale nonnegative le_one
          ((M).agentAt site) option).map
        (choiceEquiv setup leaks bounds horizon scheduler ((M).agentAt site) clear)).map
      (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm))).map
        (RecoveryOnePacket.sourceNativeChoiceEquiv setup (oldLeaks) bounds horizon (oldScheduler)
          who nativeSite.1) =
      lateComponent setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon (NativeScheduler)
        source scale nonnegative le_one who nativeSite.1 option := by
  let agent := (M).agentAt site
  let equivalent := choiceEquiv setup leaks bounds horizon scheduler agent clear
  have oldMap : (keyedComponent setup leaks bounds horizon scheduler source scale nonnegative
        le_one agent option).map equivalent =
      RecoveryOnePacket.keyedComponent setup (oldLeaks) bounds Initial horizon (oldScheduler)
        source scale nonnegative le_one
        (projectedAgent setup leaks bounds horizon scheduler agent clear) option := by
    unfold keyedComponent
    rw [dite_eq_left clear, PMF.map_comp]
    simp only [equivalent, Function.comp_def, Equiv.apply_symm_apply]
    exact PMF.map_id _
  have castVal {first second : (R).InfoState who} (same : first = second)
      (choice : (R).Choice who first) :
      (Equiv.cast (congrArg (fun input => (R).Choice who input) same) choice).1 = choice.1 := by
    cases same
    rfl
  apply pmf_map_injective Subtype.val_injective
  rw [RecoveryOnePacket.sourceNativeChoiceEquiv_map_val, PMF.map_comp]
  change ((keyedComponent setup leaks bounds horizon scheduler source scale nonnegative le_one
    agent option).map equivalent).map
      (fun choice => (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm)
        choice).1.map (RecoveryProjection.action (runtime setup) (oldLeaks))) = _
  have forgetCast : (fun choice : (R).Choice who (projectInfo site.1) =>
      (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm) choice).1.map
        (RecoveryProjection.action (runtime setup) (oldLeaks))) =
      (fun choice => choice.1.map (RecoveryProjection.action (runtime setup) (oldLeaks))) := by
    funext choice
    exact congrArg (fun response => response.map (RecoveryProjection.action (runtime setup)
      (oldLeaks))) (castVal lifted.symm choice)
  rw [forgetCast, oldMap]
  have oldClear : RecoveryProjection.ClearInput (runtime setup) (oldLeaks)
      (projectInfo site.1) := by
    rw [← lifted]
    exact RecoveryProjection.clearInput_lift (runtime setup) (oldLeaks) nativeSite.1
  have projected := RecoveryOnePacket.keyedComponent_native setup (oldLeaks) bounds horizon
    (oldScheduler) source scale nonnegative le_one
    (projectedAgent setup leaks bounds horizon scheduler agent clear) oldClear option
  have nativeInput : RecoveryProjection.information (runtime setup) (oldLeaks)
      (projectInfo site.1) = nativeSite.1 := by
    rw [← lifted, RecoveryProjection.information_liftInformation]
  change (RecoveryOnePacket.keyedComponent setup (oldLeaks) bounds Initial horizon (oldScheduler)
    source scale nonnegative le_one
    (projectedAgent setup leaks bounds horizon scheduler agent clear) option).map
      (fun choice => choice.1.map (RecoveryProjection.action (runtime setup) (oldLeaks))) =
    (lateComponent setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon (NativeScheduler)
      source scale nonnegative le_one who
      (RecoveryProjection.information (runtime setup) (oldLeaks) (projectInfo site.1)) option).map
        Subtype.val at projected
  rw [nativeInput] at projected
  exact projected

end Vegas.SequentialPhase
