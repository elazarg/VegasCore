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

/-- The actual phase component mixture maps to the actual recovery comparison
strategy law at every clear played input. -/
theorem componentStrategy_recovery_law
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup runtime leaks agent.2.1) :
    ((componentStrategy setup runtime leaks bounds horizon scheduler fallback assessment scale
      nonnegative
      le_one weights agent.1 agent.2.1).map
        (choiceEquiv setup runtime leaks bounds horizon scheduler agent clear)) =
      recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler assessment scale
        nonnegative
        le_one weights agent.1 (projectInfo agent.2.1) := by
  have atAgent : componentStrategy setup runtime leaks bounds horizon scheduler fallback
    assessment scale
      nonnegative le_one weights agent.1 agent.2.1 =
      (weights (pool setup runtime leaks bounds horizon scheduler agent)).bind
        (component setup runtime leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent) :=
    (M).agentBehavior_at (M).playedInformation fallback _ agent
  rw [atAgent]
  exact (recoveryComparisonStrategy_at_clear setup runtime leaks bounds horizon scheduler
    assessment scale
    nonnegative le_one weights agent clear).symm

omit [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler] in
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
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (M).Policy who)
    (assessment : (M).BehavioralAssessment)
    (assembled : assessment.strategy = componentStrategy setup runtime leaks bounds horizon
      scheduler
      fallback (source n) (scale n) (positive n).le (le_one n) (weights n))
    (who : Player) (site : (M).InformationSite who)
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (atSite : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (nativeSite : (N).InformationSite who)
    (lifted : RecoveryProjection.liftInformation runtime (RecoveryLeaks) nativeSite.1 =
      projectInfo site.1) :
    let agent := (M).agentAt site
    let agentClear : ClearInput setup runtime leaks agent.2.1 := by
      change ClearInput setup runtime leaks site.1
      rw [atSite]
      exact clear
    ((((assessment.strategy who site.1).map
      (choiceEquiv setup runtime leaks bounds horizon scheduler agent agentClear)).map
        (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm))).map
          (RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup (RecoveryLeaks)
            bounds horizon
              (RecoveryScheduler)
            who nativeSite.1)) =
      (nativeComparisonSequence setup runtime leaks bounds horizon scheduler source scale positive
        le_one
        weights n).strategy who nativeSite.1 := by
  classical
  intro agent agentClear
  let recoveryProfile := recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler
    (source n)
    (scale n) (positive n).le (le_one n) (weights n)
  have recoveryInput : projectInfo site.1 = some
      (past.map (PhaseRecoveryProjection.playerEntry runtime leaks (RecoveryLeaks)),
        PhaseRecoveryProjection.playerView runtime leaks (RecoveryLeaks) view) := by
    rw [atSite]
    rfl
  have played : projectInfo site.1 ∈ (R).playedInformation who :=
    projected_input_played setup runtime leaks bounds horizon scheduler agent agentClear
  have recoveryDecision : (R).IsDecisionInfo who (projectInfo site.1) := by
    let : DecidableEq ((R).InfoState who) :=
      recoveryInfoDecidableEq setup runtime leaks bounds horizon scheduler who
    unfold InformationModel.playedInformation at played
    obtain ⟨history, member, seen⟩ := Finset.mem_image.mp played
    have running := (Finset.mem_filter.mp member).2
    let recoveryPast := past.map (PhaseRecoveryProjection.playerEntry runtime leaks
        (RecoveryLeaks))
    let recoveryView := PhaseRecoveryProjection.playerView runtime leaks (RecoveryLeaks)
        view
    let action := ((RMenu).nonempty who recoveryPast recoveryView).choose
    refine ⟨⟨history, seen⟩, running, action, ?_⟩
    rw [recoveryInput]
    change ∃ response, response ∈ (RMenu).actions who recoveryPast recoveryView ∧
      (some action : Option (recoveryApplication runtime (RecoveryLeaks)).Action) = some
          response
    exact ⟨action, ((RMenu).nonempty who recoveryPast recoveryView).choose_spec, rfl⟩
  have nativeDecision : (R).IsDecisionInfo who
      (RecoveryProjection.liftInformation runtime (RecoveryLeaks) nativeSite.1) := by
    rw [lifted]
    exact recoveryDecision
  have nativeLaw : (nativeComparisonSequence setup runtime leaks bounds horizon scheduler source
    scale
      positive le_one weights n).strategy who nativeSite.1 =
      (recoveryProfile who (RecoveryProjection.liftInformation runtime (RecoveryLeaks)
        nativeSite.1)).map
          (RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup (RecoveryLeaks)
            bounds horizon
              (RecoveryScheduler)
            who nativeSite.1) := by
    apply pmf_map_injective Subtype.val_injective
    change (RecoveryOnePacket.nativeComparisonStrategy (runtime := runtime) setup (RecoveryLeaks)
      bounds horizon
      (RecoveryScheduler)
      source scale positive le_one
      (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights
        n)) n who
        nativeSite.1).map Subtype.val =
      (RecoveryOnePacket.sourceNativeProfile (runtime := runtime) setup (RecoveryLeaks) bounds
        horizon
          (RecoveryScheduler)
        recoveryProfile who nativeSite.1).map Subtype.val
    rw [RecoveryOnePacket.sourceNativeProfile_map_val]
    exact RecoveryOnePacket.nativeComparisonStrategy_at_clear (runtime := runtime) setup
      (RecoveryLeaks) bounds horizon
      (RecoveryScheduler) source scale positive le_one
      (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights
        n)) n
      (recoveryComparisonFallback setup runtime leaks bounds horizon scheduler) recoveryProfile rfl
          nativeSite
      nativeDecision
  rw [assembled, componentStrategy_recovery_law setup runtime leaks bounds horizon scheduler
    fallback
    (source n) (scale n) (positive n).le (le_one n) (weights n) agent agentClear]
  erw [policy_map_input_cast setup runtime leaks bounds horizon scheduler (recoveryProfile who)
    lifted.symm]
  exact nativeLaw.symm

end Vegas.SequentialPhase
