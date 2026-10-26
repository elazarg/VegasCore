/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseOwingOptimality
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Vanishing local gains at actual phase debt sites -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "P" => phaseApplication runtime leaks
local notation "A" => recoveryApplication runtime (recoveryLeaks setup leaks)
local notation "M" => model setup runtime leaks bounds horizon scheduler
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "projection" => PhaseRecoveryProjection.protocolState runtime leaks
    RecoveryLeaks

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- Owed source debt makes every local deviation indifferent in the actual phase game. -/
theorem component_owing_localGain_eq_zero
    (fallback : ∀ who, (M).Policy who)
    (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (positiveScale : 0 < scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (who : Player) (site : (M).InformationSite who)
    (siteClear : ClearInput setup runtime leaks site.1)
    (positive : 0 < (M).informationMass
      (componentStrategy setup runtime leaks bounds horizon scheduler fallback source scale
        positiveScale.le le_one weights) who site)
    (owing : RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds
      (RecoveryPrior) horizon
      (RecoveryScheduler)
      (projectedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) siteClear))
    (assessment : (M).BehavioralAssessment)
    (assembled : assessment.strategy = componentStrategy setup runtime leaks bounds horizon
      scheduler
      fallback source scale positiveScale.le le_one weights)
    (bayes : BehavioralAssessment.IsBayesConsistent (M) assessment
      ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
        horizon
          scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (completes : PhaseService.CompletesPlay runtime leaks (phaseInitialLaw setup) horizon
      scheduler)
    (law : PMF ((M).Choice who site.1)) :
    localGain (2 * horizon + 1) (fun final => final.state)
      (phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
      assessment site law = 0 := by
  have fixed (policy : (M).BehavioralPolicy who) := component_owing_continuation_value_eq setup
    runtime
    leaks bounds horizon scheduler fallback source scale positiveScale le_one weights who site
    siteClear positive owing assessment assembled bayes parameter utility excludedPayoff completes
    policy
  rw [localGain_eq_sub,
    localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
      (phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
      assessment site ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
        scheduler),
    localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
      (phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
      assessment site ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
        scheduler),
    fixed _, fixed _, sub_self]

end Vegas.SequentialPhase
