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
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "P" => phaseApplication (runtime setup) leaks
local notation "A" => recoveryApplication (runtime setup) (recoveryLeaks setup leaks)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks oldLeaks

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

/-- Owed source debt makes every local deviation indifferent in the actual phase game. -/
theorem component_owing_localGain_eq_zero
    (fallback : ∀ who, (M).Policy who)
    (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (positiveScale : 0 < scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (who : Player) (site : (M).InformationSite who)
    (siteClear : ClearInput setup leaks site.1)
    (positive : 0 < (M).informationMass
      (componentStrategy setup leaks bounds horizon scheduler fallback source scale
        positiveScale.le le_one weights) who site)
    (owing : RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds (oldInitial) horizon
      (oldScheduler)
      (projectedAgent setup leaks bounds horizon scheduler ((M).agentAt site) siteClear))
    (assessment : (M).BehavioralAssessment)
    (assembled : assessment.strategy = componentStrategy setup leaks bounds horizon scheduler
      fallback source scale positiveScale.le le_one weights)
    (bayes : BehavioralAssessment.IsBayesConsistent (M) assessment
      ((menu setup leaks bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initialLaw setup) horizon
      scheduler)
    (law : PMF ((M).Choice who site.1)) :
    localGain (2 * horizon + 1) (fun final => final.state)
      (phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
      assessment site law = 0 := by
  have fixed (policy : (M).BehavioralPolicy who) := component_owing_continuation_value_eq setup
    leaks bounds horizon scheduler fallback source scale positiveScale le_one weights who site
    siteClear positive owing assessment assembled bayes parameter utility excludedPayoff completes
    policy
  rw [localGain_eq_sub,
    localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
      (phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
      assessment site ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler),
    localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
      (phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
      assessment site ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler),
    fixed _, fixed _, sub_self]

end Vegas.SequentialPhase
