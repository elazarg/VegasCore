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
local notation "rawModel" => ReactiveApplication.information (A) (oldInitial) horizon (oldScheduler)
local notation "oldProtocol" => ReactiveApplication.ResponseMenu.protocol (oldMenu) (oldInitial)
  horizon (oldScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (oldInitial) horizon (oldScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks oldLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks oldLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "oldClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

open Classical in
/-- The existing local value of an actual assembled Bayesian phase assessment is
within the explicit foreign-exit error of its actual bounded physical comparison.
The payoff and original phase completion contract are retained. -/
theorem component_localValue_sub_stopped_le_foreign_exit
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (positiveScale : 0 < scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (who : Player) (site : (M).InformationSite who)
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (positive : 0 < (M).informationMass
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale
        positiveScale.le le_one weights) who site)
    (law : PMF ((M).Choice who site.1))
    (phaseAssessment : (M).BehavioralAssessment)
    (assembled : phaseAssessment.strategy = componentStrategy setup leaks bounds horizon scheduler
      fallback assessment scale positiveScale.le le_one weights)
    (bayes : BehavioralAssessment.IsBayesConsistent (M) phaseAssessment
      ((menu setup leaks bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initialLaw setup)
      horizon scheduler)
    {bound : ℝ} (nonnegativeBound : 0 ≤ bound)
    (payoffBounded : ∀ history :
      ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History,
      |phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    let oldProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment
      scale positiveScale.le le_one weights
    let agent := (M).agentAt site
    let agentClear : ClearInput setup leaks agent.2.1 := by
      change ClearInput setup leaks site.1
      rw [siteInput]
      exact clear
    let oldUpdated := Profile.update (sig := (R).behavioralSignature) oldProfile who
      ((oldProfile who).withLaw (projectInfo site.1)
        (law.map (choiceEquiv setup leaks bounds horizon scheduler agent agentClear)))
    let read := fun state : (A).ProtocolState =>
      if RecoveryPublicExclusion (setup := setup) (leaks := oldLeaks) state ∨
          RecoveryDecodedState (leaks := oldLeaks) source
            (ProtocolState.OwesFailure who setup.program) state then
        excludedPayoff who else recoveryExclusionBase parameter utility excludedPayoff state who
    let foreign := {state : (A).ProtocolState |
      (RecoveryPublicExclusion (setup := setup) (leaks := oldLeaks) state ∨
        RecoveryDecodedState (leaks := oldLeaks) source
          (ProtocolState.OwesFailure who setup.program) state) ∧
      ¬ RecoveryExcluded (setup := setup) (leaks := oldLeaks) who state ∧
      ¬ RecoveryDecodedState (leaks := oldLeaks) source
        (ProtocolState.OwesFailure who setup.program) state}
    ∃ (oldSite : (R).InformationSite who)
      (oldPositive : 0 < (R).informationMass oldProfile who oldSite),
      oldSite.1 = projectInfo site.1 ∧
      let oldBelief := (R).bayesBelief oldProfile who oldSite
        ((oldMenu).decisionInformationAntichain (oldInitial) horizon (oldScheduler) who oldSite)
        oldPositive
      let stopped := oldBelief.bind fun history =>
        ((R).runBehavioralUntil
          ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories oldUpdated
          (fun final => ¬ oldClear final.state ∨ RecoveryDecodedState (leaks := oldLeaks) source
            (ProtocolState.OwesFailure who setup.program) final.state) history.1).map History.state
      |localValue (2 * horizon + 1) (fun final => final.state)
          (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
          phaseAssessment site law - expect stopped read| ≤
        (2 * bound) * (stopped.toOuterMeasure foreign).toReal := by
  intro oldProfile agent agentClear oldUpdated read foreign
  have actualPositive : 0 < (M).informationMass phaseAssessment.strategy who site := by
    rw [assembled]
    exact positive
  have valueEq := phase_localValue_eq_bayes_terminal_expect setup leaks bounds horizon scheduler
    phaseAssessment bayes (phaseExclusionBase setup .sequential (runtime setup) leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
    who site actualPositive law
  simp only [assembled] at valueEq
  obtain ⟨oldSite, oldPositive, inputEq, near⟩ :=
    component_local_bayes_terminal_sub_stopped_le_foreign_exit setup leaks bounds horizon scheduler
      fallback assessment scale positiveScale le_one weights who site past view siteInput clear
      positive law parameter utility excludedPayoff source completes nonnegativeBound payoffBounded
      excludedBounded
  refine ⟨oldSite, oldPositive, inputEq, ?_⟩
  intro oldBelief stopped
  rw [valueEq]
  exact near

end Vegas.SequentialPhase
