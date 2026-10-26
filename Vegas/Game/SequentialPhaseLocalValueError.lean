/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseRecoveryForeignBounds
import Vegas.Game.SequentialPhaseLocalNativeBayesValueBound

/-! # Uniform original phase local-value error against one fixed native comparison site -/

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

variable {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- Every forced, debt-free phase site has one actual projected recovery comparison
site for all local laws. Its original local utility differs from the existing
native debt-stopped value by a uniformly vanishing error, under physical phase
service alone. The actual comparison weights and Bayes beliefs are retained. -/
theorem localValue_native_error_vanishes [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler)
        (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity runtime leaks (phaseInitialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion runtime leaks (phaseInitialLaw setup)
      horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    (completes : PhaseService.CompletesPlay runtime leaks (phaseInitialLaw setup)
      horizon scheduler)
    (phaseAssessments : ℕ → (M).BehavioralAssessment)
    (fallback : ℕ → ∀ who, (M).Policy who)
    (assembled : ∀ n, (phaseAssessments n).strategy =
      componentStrategy setup runtime leaks bounds horizon scheduler (fallback n) (sequence n)
        (scale n)
        (positive n).le (le_one n) (weights n))
    (mixed : ∀ n, (phaseAssessments n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (M) (phaseAssessments n)
      ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
        horizon
          scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ history :
      ((menu setup runtime leaks bounds).protocol (phaseInitialLaw setup) horizon
        scheduler).History,
      ∀ who, |phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (M).InformationSite who)
        (past : List (P).PlayerEntry) (view : (P).PlayerView)
        (atSite : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅),
      let agent := (M).agentAt site
      let agentClear : ClearInput setup runtime leaks agent.2.1 := by
        change ClearInput setup runtime leaks site.1
        rw [atSite]
        exact clear
      ¬ FreeAgent setup runtime leaks bounds horizon scheduler agent →
      ¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds
        RecoveryPrior horizon
          (RecoveryScheduler)
        (projectedAgent setup runtime leaks bounds horizon scheduler agent agentClear) →
      ∀ event : (graph setup).EventId,
        view.application.1.publicView.ownTurn? who = some event →
      let recoveryProfile := recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler
          (sequence n)
        (scale n) (positive n).le (le_one n) (weights n)
      ∃ (recoverySite : (R).InformationSite who)
        (recoveryPositive : 0 < (R).informationMass recoveryProfile who recoverySite),
        recoverySite.1 = projectInfo site.1 ∧
        ∀ law : PMF ((M).Choice who site.1),
        let recoveryUpdated := Profile.update (sig := (R).behavioralSignature) recoveryProfile who
          ((recoveryProfile who).withLaw (projectInfo site.1)
            (law.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent agentClear)))
        |localValue (2 * horizon + 1) (fun final => final.state)
            (phaseExclusionBase setup .sequential runtime leaks
              (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
            (phaseAssessments n) site law -
          expect ((R).bayesBelief recoveryProfile who recoverySite
            ((RMenu).decisionInformationAntichain RecoveryPrior horizon (RecoveryScheduler) who
                recoverySite)
            recoveryPositive) (fun history => RecoveryOnePacket.nativeDebtStoppedValue (runtime :=
              runtime) setup
                (RecoveryLeaks)
              bounds horizon (RecoveryScheduler) parameter utility excludedPayoff rawCertificate
              recoveryUpdated who history.1)| ≤ error n := by
  obtain ⟨foreignError, foreignLimit, bounded⟩ := recovery_comparison_foreign_exit_bounds setup
    runtime
    leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed scale
    positive le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely
    certificate rawCertificate
  refine ⟨fun n => (2 * payoffBound) * foreignError n, ?_, ?_⟩
  · simpa only [mul_zero] using foreignLimit.const_mul (2 * payoffBound)
  intro n who site past view atSite clear agent agentClear notFree notOwing event turn
      recoveryProfile
  have actualPositive : 0 < (M).informationMass (phaseAssessments n).strategy who site :=
    (M).informationMass_pos_of_fullSupport _ (mixed n) who site
  have positiveSite : 0 < (M).informationMass
      (componentStrategy setup runtime leaks bounds horizon scheduler (fallback n) (sequence n)
        (scale n)
        (positive n).le (le_one n) (weights n)) who site := by
    rw [← assembled n]
    exact actualPositive
  obtain ⟨recoverySite, recoveryPositive, recoveryInput, _posterior⟩ :=
      component_comparison_bayes_state_eq setup runtime
    leaks bounds horizon scheduler (fallback n) (sequence n) (scale n) (positive n) (le_one n)
    (weights n) who site past view atSite clear positiveSite
  refine ⟨recoverySite, recoveryPositive, recoveryInput, ?_⟩
  have agentEq : (R).agentAt recoverySite =
      projectedAgent setup runtime leaks bounds horizon scheduler agent agentClear := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext recoveryInput)
  have recoveryNotFree : ¬ RecoveryOnePacket.FreeAgent (runtime := runtime) setup (RecoveryLeaks)
    bounds RecoveryPrior
      horizon
      (RecoveryScheduler) ((R).agentAt recoverySite) := by
    rw [agentEq]
    exact fun free => notFree ((freeAgent_projected_iff setup runtime leaks bounds horizon scheduler
      agent agentClear).mp free)
  have recoveryNotOwing : ¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup
    (RecoveryLeaks) bounds RecoveryPrior
      horizon
      (RecoveryScheduler) ((R).agentAt recoverySite) := by
    rw [agentEq]
    exact notOwing
  let recoveryPast := past.map (PhaseRecoveryProjection.playerEntry runtime leaks
      (RecoveryLeaks))
  let recoveryView := PhaseRecoveryProjection.playerView runtime leaks (RecoveryLeaks) view
  have recoveryStateEq : recoverySite.1 = some (recoveryPast, recoveryView) := by
    rw [recoveryInput, atSite]
    rfl
  have recoveryTurn : recoveryView.application.1.publicView.ownTurn? who = some event := turn
  intro law recoveryUpdated
  obtain ⟨comparisonSite, comparisonPositive, comparisonInput, near⟩ :=
    component_localValue_sub_native_debt_stopped_le_foreign_exit setup runtime leaks bounds horizon
      scheduler (fallback n) (sequence n) (scale n) (positive n) (le_one n) (weights n) who site
      past view atSite clear positiveSite law (phaseAssessments n) (assembled n) (bayes n)
      parameter utility excludedPayoff rawCertificate completes nonnegative
      (fun history => payoffBounded history who) (excludedBounded who)
  have sitesEq : comparisonSite = recoverySite := Subtype.ext (comparisonInput.trans
      recoveryInput.symm)
  subst comparisonSite
  have small := bounded n who recoverySite recoveryNotFree recoveryNotOwing recoveryStateEq
      recoveryTurn
    ((recoveryProfile who).withLaw (projectInfo site.1)
      (law.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent agentClear)))
  exact near.trans (mul_le_mul_of_nonneg_left small (by positivity))

end Vegas.SequentialPhase
