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
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu runtime (RecoveryLeaks)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) RecoveryPrior horizon
  (RecoveryScheduler)
local notation "NP" => onePacketProtocol (runtime := runtime) setup (RecoveryLeaks) bounds horizon
  (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application (runtime := runtime) setup
  (RecoveryLeaks))
  (PMF.map RecoveryState.native (RecoveryPrior)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application (runtime :=
  runtime) setup
    (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local notation "P" => phaseApplication runtime leaks
local notation "M" => model setup runtime leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information runtime leaks
    (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

open Classical in
/-- A keyed phase decision has an actual current owner turn and an actual shared key. -/
theorem keyed_information {who : Player} (site : (M).InformationSite who)
    (keyed : KeyedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site)) :
    ∃ (past : List (P).PlayerEntry) (view : (P).PlayerView)
      (event : (graph setup).EventId) (key : LateKey (runtime := runtime) setup (RecoveryLeaks)),
      site.1 = some (past, view) ∧
      view.application.1.publicView.ownTurn? who = some event ∧
      agentKey setup runtime leaks bounds horizon scheduler ((M).agentAt site) = some key := by
  obtain ⟨nativePast, nativeView, event, atNative, pending, _activated⟩ := keyed
  have found : ∃ input, site.1 = some input := by
    cases current : site.1 with
    | none => simp [PhaseRecoveryProjection.information, RecoveryProjection.information,
        current] at atNative
    | some input => exact ⟨input, rfl⟩
  obtain ⟨⟨past, view⟩, atSite⟩ := found
  have nativePending := pending
  rw [atNative] at nativePending
  have turn := (pendingEvent_spec (runtime := runtime) (setup := setup) nativePending).1
  have nativePair := atNative
  rw [atSite] at nativePair
  simp only [PhaseRecoveryProjection.information, RecoveryProjection.information, Option.map_some]
    at nativePair
  have views := congrArg Prod.snd (Option.some.inj nativePair)
  change RecoveryProjection.playerView runtime (RecoveryLeaks)
    (PhaseRecoveryProjection.playerView runtime leaks (RecoveryLeaks) view) = nativeView
        at views
  rw [← views] at turn
  refine ⟨past, view, event, LateKey.ofView (runtime := runtime) setup (RecoveryLeaks) who
    nativePast nativeView, atSite,
    turn, ?_⟩
  change lateKey (runtime := runtime) setup (RecoveryLeaks) who
    (RecoveryProjection.information runtime (RecoveryLeaks) (projectInfo site.1)) = _
  rw [atNative]
  rfl

open Classical in
/-- The actual keyed phase law maps to exactly the same native late option,
including all menu casts forced by the fixed comparison information fiber. -/
theorem keyedComponent_native_choice
    (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {who : Player} (site : (M).InformationSite who)
    (clear : ClearInput setup runtime leaks site.1) (nativeSite : (N).InformationSite who)
    (lifted : RecoveryProjection.liftInformation runtime (RecoveryLeaks) nativeSite.1 =
      projectInfo site.1) (option : LateOption slots) :
    (((keyedComponent setup runtime leaks bounds horizon scheduler source scale nonnegative le_one
          ((M).agentAt site) option).map
        (choiceEquiv setup runtime leaks bounds horizon scheduler ((M).agentAt site) clear)).map
      (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm))).map
        (RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup (RecoveryLeaks)
          bounds horizon
            (RecoveryScheduler)
          who nativeSite.1) =
      lateComponent (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
        horizon (NativeScheduler)
        source scale nonnegative le_one who nativeSite.1 option := by
  let agent := (M).agentAt site
  let equivalent := choiceEquiv setup runtime leaks bounds horizon scheduler agent clear
  have recoveryComponentLaw : (keyedComponent setup runtime leaks bounds horizon scheduler source
    scale
      nonnegative
        le_one agent option).map equivalent =
      RecoveryOnePacket.keyedComponent (runtime := runtime) setup (RecoveryLeaks) bounds
        RecoveryPrior horizon
          (RecoveryScheduler)
        source scale nonnegative le_one
        (projectedAgent setup runtime leaks bounds horizon scheduler agent clear) option := by
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
  change ((keyedComponent setup runtime leaks bounds horizon scheduler source scale nonnegative
    le_one
    agent option).map equivalent).map
      (fun choice => (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm)
        choice).1.map (RecoveryProjection.action runtime (RecoveryLeaks))) = _
  have forgetCast : (fun choice : (R).Choice who (projectInfo site.1) =>
      (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm) choice).1.map
        (RecoveryProjection.action runtime (RecoveryLeaks))) =
      (fun choice => choice.1.map (RecoveryProjection.action runtime (RecoveryLeaks))) := by
    funext choice
    exact congrArg (fun response => response.map (RecoveryProjection.action runtime
      (RecoveryLeaks))) (castVal lifted.symm choice)
  rw [forgetCast, recoveryComponentLaw]
  have recoveryCleared : RecoveryProjection.ClearInput runtime (RecoveryLeaks)
      (projectInfo site.1) := by
    rw [← lifted]
    exact RecoveryProjection.clearInput_lift runtime (RecoveryLeaks) nativeSite.1
  have projected := RecoveryOnePacket.keyedComponent_native (runtime := runtime) setup
    (RecoveryLeaks) bounds horizon
    (RecoveryScheduler) source scale nonnegative le_one
    (projectedAgent setup runtime leaks bounds horizon scheduler agent clear) recoveryCleared option
  have nativeInput : RecoveryProjection.information runtime (RecoveryLeaks)
      (projectInfo site.1) = nativeSite.1 := by
    rw [← lifted, RecoveryProjection.information_liftInformation]
  change (RecoveryOnePacket.keyedComponent (runtime := runtime) setup (RecoveryLeaks) bounds
    RecoveryPrior horizon
      (RecoveryScheduler)
    source scale nonnegative le_one
    (projectedAgent setup runtime leaks bounds horizon scheduler agent clear) option).map
      (fun choice => choice.1.map (RecoveryProjection.action runtime (RecoveryLeaks))) =
    (lateComponent (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
      horizon (NativeScheduler)
      source scale nonnegative le_one who
      (RecoveryProjection.information runtime (RecoveryLeaks) (projectInfo site.1))
          option).map
        Subtype.val at projected
  rw [nativeInput] at projected
  exact projected

end Vegas.SequentialPhase
