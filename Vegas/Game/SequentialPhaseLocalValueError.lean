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

local instance localValuePosteriorComparisonHistory : Fintype ((RMenu).protocol
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).History :=
  sourceHistoryFintype setup leaks bounds horizon scheduler

local instance localValuePosteriorComparisonInformation (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds
      ((Vegas.initialLaw setup).map (fun native =>
        (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).InfoState who) :=
  sourceInfoDecidableEq setup leaks bounds horizon scheduler who

local instance localValuePosteriorComparisonNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance localValuePosteriorNativeInformation (who : Player) :
    DecidableEq ((N).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

local instance localValuePosteriorRecoveryNature :
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) (oldScheduler) :=
  recoveryNature setup leaks scheduler

local instance localValuePosteriorNativeHistory : Fintype (NP).History :=
  @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (NMenu) (Vegas.initialLaw setup)
    horizon (NativeScheduler) inferInstance (nativeNature setup leaks scheduler)

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

variable {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- Every forced, debt-free phase site has one actual projected old comparison
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
      (combinedFloor setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (initialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (initialLaw setup)
      horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initialLaw setup)
      horizon scheduler)
    (phaseAssessments : ℕ → (M).BehavioralAssessment)
    (fallback : ℕ → ∀ who, (M).Policy who)
    (assembled : ∀ n, (phaseAssessments n).strategy =
      componentStrategy setup leaks bounds horizon scheduler (fallback n) (sequence n) (scale n)
        (positive n).le (le_one n) (weights n))
    (mixed : ∀ n, (phaseAssessments n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (M) (phaseAssessments n)
      ((menu setup leaks bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ history :
      ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History,
      ∀ who, |phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (M).InformationSite who)
        (past : List (P).PlayerEntry) (view : (P).PlayerView)
        (atSite : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅),
      let agent := (M).agentAt site
      let agentClear : ClearInput setup leaks agent.2.1 := by
        change ClearInput setup leaks site.1
        rw [atSite]
        exact clear
      ¬ FreeAgent setup leaks bounds horizon scheduler agent →
      ¬ RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds Initial horizon (oldScheduler)
        (projectedAgent setup leaks bounds horizon scheduler agent agentClear) →
      ∀ event : (graph setup).EventId,
        view.application.1.publicView.ownTurn? who = some event →
      let oldProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler (sequence n)
        (scale n) (positive n).le (le_one n) (weights n)
      ∃ (oldSite : (R).InformationSite who)
        (oldPositive : 0 < (R).informationMass oldProfile who oldSite),
        oldSite.1 = projectInfo site.1 ∧
        ∀ law : PMF ((M).Choice who site.1),
        let oldUpdated := Profile.update (sig := (R).behavioralSignature) oldProfile who
          ((oldProfile who).withLaw (projectInfo site.1)
            (law.map (choiceEquiv setup leaks bounds horizon scheduler agent agentClear)))
        |localValue (2 * horizon + 1) (fun final => final.state)
            (phaseExclusionBase setup .sequential (runtime setup) leaks
              (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
            (phaseAssessments n) site law -
          expect ((R).bayesBelief oldProfile who oldSite
            ((RMenu).decisionInformationAntichain Initial horizon (oldScheduler) who oldSite)
            oldPositive) (fun history => RecoveryOnePacket.nativeDebtStoppedValue setup (oldLeaks)
              bounds horizon (oldScheduler) parameter utility excludedPayoff rawCertificate
              oldUpdated who history.1)| ≤ error n := by
  obtain ⟨foreignError, foreignLimit, bounded⟩ := recovery_comparison_foreign_exit_bounds setup
    leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed scale
    positive le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely
    certificate rawCertificate
  refine ⟨fun n => (2 * payoffBound) * foreignError n, ?_, ?_⟩
  · simpa only [mul_zero] using foreignLimit.const_mul (2 * payoffBound)
  intro n who site past view atSite clear agent agentClear notFree notOwing event turn oldProfile
  have actualPositive : 0 < (M).informationMass (phaseAssessments n).strategy who site :=
    (M).informationMass_pos_of_fullSupport _ (mixed n) who site
  have positiveSite : 0 < (M).informationMass
      (componentStrategy setup leaks bounds horizon scheduler (fallback n) (sequence n) (scale n)
        (positive n).le (le_one n) (weights n)) who site := by
    rw [← assembled n]
    exact actualPositive
  obtain ⟨oldSite, oldPositive, oldInput, _posterior⟩ := component_comparison_bayes_state_eq setup
    leaks bounds horizon scheduler (fallback n) (sequence n) (scale n) (positive n) (le_one n)
    (weights n) who site past view atSite clear positiveSite
  refine ⟨oldSite, oldPositive, oldInput, ?_⟩
  have agentEq : (R).agentAt oldSite =
      projectedAgent setup leaks bounds horizon scheduler agent agentClear := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext oldInput)
  have oldNotFree : ¬ RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler) ((R).agentAt oldSite) := by
    rw [agentEq]
    exact fun free => notFree ((freeAgent_projected_iff setup leaks bounds horizon scheduler
      agent agentClear).mp free)
  have oldNotOwing : ¬ RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler) ((R).agentAt oldSite) := by
    rw [agentEq]
    exact notOwing
  let oldPast := past.map (PhaseRecoveryProjection.playerEntry (runtime setup) leaks (oldLeaks))
  let oldView := PhaseRecoveryProjection.playerView (runtime setup) leaks (oldLeaks) view
  have oldAt : oldSite.1 = some (oldPast, oldView) := by
    rw [oldInput, atSite]
    rfl
  have oldTurn : oldView.application.1.publicView.ownTurn? who = some event := turn
  intro law oldUpdated
  obtain ⟨comparisonSite, comparisonPositive, comparisonInput, near⟩ :=
    component_localValue_sub_native_debt_stopped_le_foreign_exit setup leaks bounds horizon
      scheduler (fallback n) (sequence n) (scale n) (positive n) (le_one n) (weights n) who site
      past view atSite clear positiveSite law (phaseAssessments n) (assembled n) (bayes n)
      parameter utility excludedPayoff rawCertificate completes nonnegative
      (fun history => payoffBounded history who) (excludedBounded who)
  have sitesEq : comparisonSite = oldSite := Subtype.ext (comparisonInput.trans oldInput.symm)
  subst comparisonSite
  have small := bounded n who oldSite oldNotFree oldNotOwing oldAt oldTurn
    ((oldProfile who).withLaw (projectInfo site.1)
      (law.map (choiceEquiv setup leaks bounds horizon scheduler agent agentClear)))
  exact near.trans (mul_le_mul_of_nonneg_left small (by positivity))

end Vegas.SequentialPhase
