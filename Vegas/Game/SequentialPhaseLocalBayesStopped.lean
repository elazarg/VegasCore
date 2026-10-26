/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonBayes
import Vegas.Game.SequentialPhaseLocalStopped
import Interaction.ReactiveResponseBelief
import Interaction.ReactiveResponseStopped

/-! # Actual local continuation kernels from matched Bayes states -/

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
local notation "rawModel" => ReactiveApplication.information (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "RecoveryProtocol" => ReactiveApplication.ResponseMenu.protocol (RecoveryMenu)
    (RecoveryPrior)
  horizon (RecoveryScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState runtime leaks
    RecoveryLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information runtime leaks
    RecoveryLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "RecoveryClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- At a genuine clear information site, actual Bayes beliefs followed by any
focal local law have the same complete physical stopped endpoint distribution.
The recovery positive mass is derived from the actual comparison factory. -/
theorem component_local_bayes_stopped_state_eq
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (positiveScale : 0 < scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (who : Player) (site : (M).InformationSite who)
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (positive : 0 < (M).informationMass
      (componentStrategy setup runtime leaks bounds horizon scheduler fallback assessment scale
        positiveScale.le le_one weights) who site)
    (law : PMF ((M).Choice who site.1)) (guard : (A).ProtocolState → Prop) :
    let phaseProfile := componentStrategy setup runtime leaks bounds horizon scheduler fallback
      assessment
      scale positiveScale.le le_one weights
    let recoveryProfile := recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler
        assessment
      scale positiveScale.le le_one weights
    let agent := (M).agentAt site
    let agentClear : ClearInput setup runtime leaks agent.2.1 := by
      change ClearInput setup runtime leaks site.1
      rw [siteInput]
      exact clear
    let phaseUpdated := Profile.update (sig := (M).behavioralSignature) phaseProfile who
      ((phaseProfile who).withLaw site.1 law)
    let recoveryUpdated := Profile.update (sig := (R).behavioralSignature) recoveryProfile who
      ((recoveryProfile who).withLaw (projectInfo site.1)
        (law.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent agentClear)))
    ∃ (recoverySite : (R).InformationSite who)
      (recoveryPositive : 0 < (R).informationMass recoveryProfile who recoverySite),
      recoverySite.1 = projectInfo site.1 ∧
      (((M).bayesBelief phaseProfile who site
        ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
          horizon
            scheduler
          who site) positive).bind fun history =>
        ((M).runBehavioralUntil
          ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
            scheduler).wellFoundedHistories phaseUpdated
          (fun final => ¬ phaseClear final.state ∨ guard (projection final.state)) history.1).map
          (fun final => projection final.state)) =
      (((R).bayesBelief recoveryProfile who recoverySite
        ((RecoveryMenu).decisionInformationAntichain (RecoveryPrior) horizon (RecoveryScheduler) who
            recoverySite)
        recoveryPositive).bind fun history =>
        ((R).runBehavioralUntil
          ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
              recoveryUpdated
          (fun final => ¬ RecoveryClear final.state ∨ guard final.state) history.1).map
            History.state) := by
  intro phaseProfile recoveryProfile agent agentClear phaseUpdated recoveryUpdated
  obtain ⟨recoverySite, recoveryPositive, inputEq, posteriorEq⟩ :=
    component_comparison_bayes_state_eq setup runtime leaks bounds horizon scheduler fallback
      assessment
      scale positiveScale le_one weights who site past view siteInput clear positive
  refine ⟨recoverySite, recoveryPositive, inputEq, ?_⟩
  apply bind_eq_of_map_eq _ _ (fun history => projection history.1.state)
    (fun history => history.1.state) posteriorEq
  intro first _firstSupported second _secondSupported same
  exact component_local_comparison_run_until_exclusion_or_guard_map_state setup runtime leaks bounds
    horizon scheduler fallback assessment scale positiveScale.le le_one weights agent agentClear law
      guard first.1 second.1 same

end Vegas.SequentialPhase
