/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseBayesLocalValue

/-! # Original local phase values and actual physical stopped comparisons -/

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

open Classical in
/-- The existing local value of an actual assembled Bayesian phase assessment is
within the explicit foreign-exit error of its actual bounded physical comparison.
The payoff and original phase completion contract are retained. -/
theorem component_localValue_sub_stopped_le_foreign_exit
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
    (law : PMF ((M).Choice who site.1))
    (phaseAssessment : (M).BehavioralAssessment)
    (assembled : phaseAssessment.strategy = componentStrategy setup runtime leaks bounds horizon
      scheduler
      fallback assessment scale positiveScale.le le_one weights)
    (bayes : BehavioralAssessment.IsBayesConsistent (M) phaseAssessment
      ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
        horizon
          scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program)
    (completes : PhaseService.CompletesPlay runtime leaks (phaseInitialLaw setup)
      horizon scheduler)
    {bound : ℝ} (nonnegativeBound : 0 ≤ bound)
    (payoffBounded : ∀ history :
      ((menu setup runtime leaks bounds).protocol (phaseInitialLaw setup) horizon
        scheduler).History,
      |phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    let recoveryProfile := recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler
        assessment
      scale positiveScale.le le_one weights
    let agent := (M).agentAt site
    let agentClear : ClearInput setup runtime leaks agent.2.1 := by
      change ClearInput setup runtime leaks site.1
      rw [siteInput]
      exact clear
    let recoveryUpdated := Profile.update (sig := (R).behavioralSignature) recoveryProfile who
      ((recoveryProfile who).withLaw (projectInfo site.1)
        (law.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent agentClear)))
    let read := fun state : (A).ProtocolState =>
      if RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := RecoveryLeaks)
        state ∨
          RecoveryDecodedState (runtime := runtime) (leaks := RecoveryLeaks) source
            (ProtocolState.OwesFailure who setup.program) state then
        excludedPayoff who else recoveryExclusionBase (runtime := runtime) parameter utility
          excludedPayoff state who
    let foreign := {state : (A).ProtocolState |
      (RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := RecoveryLeaks)
        state ∨
        RecoveryDecodedState (runtime := runtime) (leaks := RecoveryLeaks) source
          (ProtocolState.OwesFailure who setup.program) state) ∧
      ¬ RecoveryExcluded (runtime := runtime) (setup := setup) (leaks := RecoveryLeaks) who state ∧
      ¬ RecoveryDecodedState (runtime := runtime) (leaks := RecoveryLeaks) source
        (ProtocolState.OwesFailure who setup.program) state}
    ∃ (recoverySite : (R).InformationSite who)
      (recoveryPositive : 0 < (R).informationMass recoveryProfile who recoverySite),
      recoverySite.1 = projectInfo site.1 ∧
      let recoveryBelief := (R).bayesBelief recoveryProfile who recoverySite
        ((RecoveryMenu).decisionInformationAntichain (RecoveryPrior) horizon (RecoveryScheduler) who
            recoverySite)
        recoveryPositive
      let stopped := recoveryBelief.bind fun history =>
        ((R).runBehavioralUntil
          ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
              recoveryUpdated
          (fun final => ¬ RecoveryClear final.state ∨ RecoveryDecodedState (runtime := runtime)
            (leaks := RecoveryLeaks)
              source
            (ProtocolState.OwesFailure who setup.program) final.state) history.1).map History.state
      |localValue (2 * horizon + 1) (fun final => final.state)
          (phaseExclusionBase setup .sequential runtime leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
          phaseAssessment site law - expect stopped read| ≤
        (2 * bound) * (stopped.toOuterMeasure foreign).toReal := by
  intro recoveryProfile agent agentClear recoveryUpdated read foreign
  have actualPositive : 0 < (M).informationMass phaseAssessment.strategy who site := by
    rw [assembled]
    exact positive
  have valueEq := phase_localValue_eq_bayes_terminal_expect setup runtime leaks bounds horizon
    scheduler
    phaseAssessment bayes (phaseExclusionBase setup .sequential runtime leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
    who site actualPositive law
  simp only [assembled] at valueEq
  obtain ⟨recoverySite, recoveryPositive, inputEq, near⟩ :=
    component_local_bayes_terminal_sub_stopped_le_foreign_exit setup runtime leaks bounds horizon
      scheduler
      fallback assessment scale positiveScale le_one weights who site past view siteInput clear
      positive law parameter utility excludedPayoff source completes nonnegativeBound payoffBounded
      excludedBounded
  refine ⟨recoverySite, recoveryPositive, inputEq, ?_⟩
  intro recoveryBelief stopped
  rw [valueEq]
  exact near

end Vegas.SequentialPhase
