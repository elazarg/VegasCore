/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonPolicy
import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.RecoveryNativeStrategy

/-! # Actual phase and native baseline strategy laws at a shared information site -/

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

local instance baselinePosteriorComparisonHistory : Fintype ((RMenu).protocol
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).History :=
  sourceHistoryFintype setup leaks bounds horizon scheduler

local instance baselinePosteriorComparisonInformation (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds
      ((Vegas.initialLaw setup).map (fun native =>
        (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).InfoState who) :=
  sourceInfoDecidableEq setup leaks bounds horizon scheduler who

local instance baselinePosteriorComparisonNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance baselinePosteriorNativeInformation (who : Player) :
    DecidableEq ((N).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

local instance baselinePosteriorRecoveryNature :
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) (oldScheduler) :=
  recoveryNature setup leaks scheduler

local instance baselinePosteriorNativeHistory : Fintype (NP).History :=
  @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (NMenu) (Vegas.initialLaw setup)
    horizon (NativeScheduler) inferInstance (nativeNature setup leaks scheduler)

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq


/-- The actual phase component mixture maps to the actual recovery comparison
strategy law at every clear played input. -/
theorem componentStrategy_recovery_law
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    ((componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
      le_one weights agent.1 agent.2.1).map
        (choiceEquiv setup leaks bounds horizon scheduler agent clear)) =
      recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights agent.1 (projectInfo agent.2.1) := by
  have atAgent : componentStrategy setup leaks bounds horizon scheduler fallback assessment scale
      nonnegative le_one weights agent.1 agent.2.1 =
      (weights (pool setup leaks bounds horizon scheduler agent)).bind
        (component setup leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent) :=
    (M).agentBehavior_at (M).playedInformation fallback _ agent
  rw [atAgent]
  exact (recoveryComparisonStrategy_at_clear setup leaks bounds horizon scheduler assessment scale
    nonnegative le_one weights agent clear).symm

omit [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler] in
private theorem policy_map_input_cast {who : Player} (policy : (R).BehavioralPolicy who)
    {first second : (R).InfoState who} (same : first = second) :
    (policy first).map (Equiv.cast (congrArg (fun input => (R).Choice who input) same)) =
      policy second := by
  subst second
  simp only [Equiv.cast_refl, Equiv.coe_refl, PMF.map_id]

/-- At the fixed native information site, the exact composed choice map sends
the original phase baseline to the actual native comparison baseline. -/
theorem phase_strategy_native_law
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (M).Policy who)
    (assessment : (M).BehavioralAssessment)
    (assembled : assessment.strategy = componentStrategy setup leaks bounds horizon scheduler
      fallback (source n) (scale n) (positive n).le (le_one n) (weights n))
    (who : Player) (site : (M).InformationSite who)
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (atSite : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (nativeSite : (N).InformationSite who)
    (lifted : RecoveryProjection.liftInformation (runtime setup) (oldLeaks) nativeSite.1 =
      projectInfo site.1) :
    let agent := (M).agentAt site
    let agentClear : ClearInput setup leaks agent.2.1 := by
      change ClearInput setup leaks site.1
      rw [atSite]
      exact clear
    ((((assessment.strategy who site.1).map
      (choiceEquiv setup leaks bounds horizon scheduler agent agentClear)).map
        (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm))).map
          (RecoveryOnePacket.sourceNativeChoiceEquiv setup (oldLeaks) bounds horizon (oldScheduler)
            who nativeSite.1)) =
      (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights n).strategy who nativeSite.1 := by
  classical
  intro agent agentClear
  let oldProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler (source n)
    (scale n) (positive n).le (le_one n) (weights n)
  have oldInput : projectInfo site.1 = some
      (past.map (PhaseRecoveryProjection.playerEntry (runtime setup) leaks (oldLeaks)),
        PhaseRecoveryProjection.playerView (runtime setup) leaks (oldLeaks) view) := by
    rw [atSite]
    rfl
  have played : projectInfo site.1 ∈ (R).playedInformation who :=
    projected_input_played setup leaks bounds horizon scheduler agent agentClear
  have oldDecision : (R).IsDecisionInfo who (projectInfo site.1) := by
    let : DecidableEq ((R).InfoState who) :=
      recoveryInfoDecidableEq setup leaks bounds horizon scheduler who
    unfold InformationModel.playedInformation at played
    obtain ⟨history, member, seen⟩ := Finset.mem_image.mp played
    have running := (Finset.mem_filter.mp member).2
    let oldPast := past.map (PhaseRecoveryProjection.playerEntry (runtime setup) leaks (oldLeaks))
    let oldView := PhaseRecoveryProjection.playerView (runtime setup) leaks (oldLeaks) view
    let action := ((RMenu).nonempty who oldPast oldView).choose
    refine ⟨⟨history, seen⟩, running, action, ?_⟩
    rw [oldInput]
    change ∃ response, response ∈ (RMenu).actions who oldPast oldView ∧
      (some action : Option (recoveryApplication (runtime setup) (oldLeaks)).Action) = some response
    exact ⟨action, ((RMenu).nonempty who oldPast oldView).choose_spec, rfl⟩
  have nativeDecision : (R).IsDecisionInfo who
      (RecoveryProjection.liftInformation (runtime setup) (oldLeaks) nativeSite.1) := by
    rw [lifted]
    exact oldDecision
  have nativeLaw : (nativeComparisonSequence setup leaks bounds horizon scheduler source scale
      positive le_one weights n).strategy who nativeSite.1 =
      (oldProfile who (RecoveryProjection.liftInformation (runtime setup) (oldLeaks)
        nativeSite.1)).map
          (RecoveryOnePacket.sourceNativeChoiceEquiv setup (oldLeaks) bounds horizon (oldScheduler)
            who nativeSite.1) := by
    apply pmf_map_injective Subtype.val_injective
    change (RecoveryOnePacket.nativeComparisonStrategy setup (oldLeaks) bounds horizon
      (oldScheduler)
      source scale positive le_one
      (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n who
        nativeSite.1).map Subtype.val =
      (RecoveryOnePacket.sourceNativeProfile setup (oldLeaks) bounds horizon (oldScheduler)
        oldProfile who nativeSite.1).map Subtype.val
    rw [RecoveryOnePacket.sourceNativeProfile_map_val]
    exact RecoveryOnePacket.nativeComparisonStrategy_at_clear setup (oldLeaks) bounds horizon
      (oldScheduler) source scale positive le_one
      (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n
      (recoveryComparisonFallback setup leaks bounds horizon scheduler) oldProfile rfl nativeSite
      nativeDecision
  rw [assembled, componentStrategy_recovery_law setup leaks bounds horizon scheduler fallback
    (source n) (scale n) (positive n).le (le_one n) (weights n) agent agentClear]
  erw [policy_map_input_cast setup leaks bounds horizon scheduler (oldProfile who) lifted.symm]
  exact nativeLaw.symm

end Vegas.SequentialPhase
