/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalBayesStopped
import Vegas.Game.SequentialPhaseStoppedPayoffBelief
import Vegas.Game.SequentialPhaseStoppedPayoffHistory
import GameTheoryExtensions.Math.Probability.ExpectationContraction

/-! # Original Bayesian phase continuation payoff and physical stopped values -/

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
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "P" => phaseApplication (runtime setup) leaks
local notation "A" => recoveryApplication (runtime setup) (recoveryLeaks setup leaks)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu (runtime setup) (RecoveryLeaks) bounds
local notation "rawModel" => ReactiveApplication.information (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "RecoveryProtocol" => ReactiveApplication.ResponseMenu.protocol (RecoveryMenu)
    (RecoveryPrior)
  horizon (RecoveryScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks
    RecoveryLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks
    RecoveryLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "RecoveryClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

open Classical in
/-- At every actual clear positive phase site, the original Bayesian continuation
payoff for an arbitrary local law differs from the actual bounded counterpart's
physical debt-stopped value only by its foreign physical exclusion mass. -/
theorem component_local_bayes_terminal_sub_stopped_le_foreign_exit
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
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (phaseInitialLaw setup)
      horizon scheduler)
    {bound : ℝ} (nonnegativeBound : 0 ≤ bound)
    (payoffBounded : ∀ history :
      ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History,
      |phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    let phaseProfile := componentStrategy setup leaks bounds horizon scheduler fallback assessment
      scale positiveScale.le le_one weights
    let recoveryProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler
        assessment
      scale positiveScale.le le_one weights
    let agent := (M).agentAt site
    let agentClear : ClearInput setup leaks agent.2.1 := by
      change ClearInput setup leaks site.1
      rw [siteInput]
      exact clear
    let phaseUpdated := Profile.update (sig := (M).behavioralSignature) phaseProfile who
      ((phaseProfile who).withLaw site.1 law)
    let recoveryUpdated := Profile.update (sig := (R).behavioralSignature) recoveryProfile who
      ((recoveryProfile who).withLaw (projectInfo site.1)
        (law.map (choiceEquiv setup leaks bounds horizon scheduler agent agentClear)))
    let phaseBelief := (M).bayesBelief phaseProfile who site
      ((menu setup leaks bounds).decisionInformationAntichain (phaseInitialLaw setup) horizon
          scheduler
        who site) positive
    let read := fun state : (A).ProtocolState =>
      if RecoveryPublicExclusion (setup := setup) (leaks := RecoveryLeaks) state ∨
          RecoveryDecodedState (leaks := RecoveryLeaks) source
            (ProtocolState.OwesFailure who setup.program) state then
        excludedPayoff who else recoveryExclusionBase parameter utility excludedPayoff state who
    let foreign := {state : (A).ProtocolState |
      (RecoveryPublicExclusion (setup := setup) (leaks := RecoveryLeaks) state ∨
        RecoveryDecodedState (leaks := RecoveryLeaks) source
          (ProtocolState.OwesFailure who setup.program) state) ∧
      ¬ RecoveryExcluded (setup := setup) (leaks := RecoveryLeaks) who state ∧
      ¬ RecoveryDecodedState (leaks := RecoveryLeaks) source
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
          (fun final => ¬ RecoveryClear final.state ∨ RecoveryDecodedState (leaks := RecoveryLeaks)
              source
            (ProtocolState.OwesFailure who setup.program) final.state) history.1).map History.state
      |expect phaseBelief (fun history => expect ((M).runBehavioralTerminalFrom
          ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
            scheduler).wellFoundedHistories phaseUpdated history.1)
          (fun final => phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
              final.state who)) - expect stopped read| ≤
        (2 * bound) * (stopped.toOuterMeasure foreign).toReal := by
  intro phaseProfile recoveryProfile agent agentClear phaseUpdated recoveryUpdated phaseBelief read
      foreign
  let guard := fun state : (A).ProtocolState => RecoveryDecodedState (leaks := RecoveryLeaks) source
    (ProtocolState.OwesFailure who setup.program) state
  obtain ⟨recoverySite, recoveryPositive, inputEq, stoppedEq⟩ :=
    component_local_bayes_stopped_state_eq setup leaks bounds horizon scheduler fallback assessment
      scale positiveScale le_one weights who site past view siteInput clear positive law guard
  refine ⟨recoverySite, recoveryPositive, inputEq, ?_⟩
  intro recoveryBelief stopped
  let kernel := (M).runBehavioralUntil
    ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
        scheduler).wellFoundedHistories
    phaseUpdated (fun history => PhaseDebtStopped setup leaks source who history.state)
  let phaseJoint := phaseBelief.bind (fun history => kernel history.1)
  let phaseForeign := {history :
      ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History |
    PhaseDebtStopped setup leaks source who history.state ∧
      ¬ PhaseExcluded setup .sequential (runtime setup) leaks who history.state ∧
      ¬ PhaseOwesFailure setup leaks source who history.state}
  have stopEq : (fun history :
      ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History =>
        PhaseDebtStopped setup leaks source who history.state) =
      fun history => ¬ phaseClear history.state ∨ guard (projection history.state) := by
    funext history
    unfold PhaseDebtStopped
    rw [phaseOwesFailure_eq_projected setup leaks RecoveryLeaks]
    rfl
  have jointEq : phaseJoint.map (fun history => projection history.state) = stopped := by
    dsimp only [phaseJoint, kernel]
    rw [stopEq, PMF.map_bind]
    exact stoppedEq
  have readEq : expect stopped read = expect phaseBelief (fun history =>
      expect (kernel history.1) (fun final => phaseDebtStoppedPayoff setup leaks parameter utility
        excludedPayoff source who final.state)) := by
    rw [← jointEq, expect_map, expect_bind_of_finite]
    apply expect_congr_on_support
    intro history _supported
    apply expect_congr_on_support
    intro final _finalSupported
    exact (phaseDebtStoppedPayoff_history_eq_projected setup leaks RecoveryLeaks
      (sequentialRuntimePhasePlan setup.program) (setup.initialLaw.map setup.eventInputs) horizon
      scheduler (menu setup leaks bounds) parameter utility excludedPayoff source who final).symm
  have eventEq : phaseForeign =
      (fun history => projection history.state) ⁻¹' foreign := by
    ext history
    exact phase_foreign_debt_exit_eq_projected setup leaks RecoveryLeaks source who history.state
  have massEq : (phaseJoint.toOuterMeasure phaseForeign).toReal =
      (stopped.toOuterMeasure foreign).toReal := by
    rw [← jointEq, PMF.toOuterMeasure_map_apply, eventEq]
  have near := phase_belief_expect_abs_sub_debt_stopped_le_foreign_exit setup leaks
    (sequentialRuntimePhasePlan setup.program) (sequentialRuntimePhasePlan_singleton setup.program)
    (setup.initialLaw.map setup.eventInputs) horizon scheduler parameter utility excludedPayoff
    source (menu setup leaks bounds) completes
    ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
        scheduler).wellFoundedHistories
    phaseUpdated who nonnegativeBound payoffBounded excludedBounded (phaseBelief.map Subtype.val)
  simp only [expect_map, PMF.bind_map, Function.comp_def] at near
  change expect phaseBelief _ ≤
    (2 * bound) * (phaseJoint.toOuterMeasure phaseForeign).toReal at near
  rw [massEq] at near
  rw [readEq]
  exact (abs_expect_sub_le_expect_abs_sub phaseBelief _ _ (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)).trans near

end Vegas.SequentialPhase
