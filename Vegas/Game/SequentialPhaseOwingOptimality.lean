/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonBayes
import Vegas.Game.SequentialPhaseDecodedDebt
import Vegas.Game.SequentialPhaseStoppedPayoffProjection
import Vegas.Game.RecoveryDebtUniformity

/-! # Whole-policy indifference at actual phase debt sites -/

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

/-- Owed source debt at the actual projected input fixes the phase continuation
value for every whole policy, including policies reading future archived data. -/
theorem component_owing_continuation_value_eq
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
    (alternative : (M).BehavioralPolicy who) :
    (assessment.continuationContext
      ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
      site (fun final => phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          final.state who)).value alternative = excludedPayoff who := by
  classical
  let sourceInitial := (Vegas.initialLaw setup).map
    (fun native => (⟨native, ∅⟩ : RecoveryState (graph setup)))
  let : Fintype ((oldMenu).protocol sourceInitial horizon (oldScheduler)).History := by
    have nature : (A).FiniteNature sourceInitial (oldScheduler) :=
      recoveryNature setup leaks scheduler
    exact @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (oldMenu) sourceInitial
      horizon (oldScheduler) inferInstance nature
  cases input : site.1 with
  | none => rw [input] at siteClear; exact siteClear.elim
  | some data =>
      rcases data with ⟨past, view⟩
      have viewClear : view.application.2.excluded = ∅ := by
        rw [input] at siteClear
        exact siteClear
      obtain ⟨oldSite, oldPositive, oldInput, stateLaw⟩ := component_comparison_bayes_state_eq setup
        leaks bounds horizon scheduler fallback source scale positiveScale le_one weights who site
        past view input viewClear positive
      let oldProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler source scale
        positiveScale.le le_one weights
      let phaseProfile := componentStrategy setup leaks bounds horizon scheduler fallback source
        scale positiveScale.le le_one weights
      let phaseBelief := (M).bayesBelief phaseProfile who site
        ((menu setup leaks bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler
          who site) positive
      let oldBelief := (R).bayesBelief oldProfile who oldSite
        ((oldMenu).decisionInformationAntichain (oldInitial) horizon (oldScheduler) who oldSite)
        oldPositive
      have sameAgent : (R).agentAt oldSite =
          projectedAgent setup leaks bounds horizon scheduler ((M).agentAt site) siteClear := by
        apply congrArg (Sigma.mk who)
        apply Subtype.ext
        exact oldInput
      have oldOwing : RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds (oldInitial) horizon
          (oldScheduler) ((R).agentAt oldSite) := sameAgent.symm ▸ owing
      have oldAll (state : (A).ProtocolState)
          (supported : state ∈ (oldBelief.map (fun history => history.1.state)).support) :
          RecoveryDecodedState (leaks := oldLeaks) (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) state := by
        obtain ⟨history, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        exact RecoveryOnePacket.owingAgent_allHistories setup (oldLeaks) bounds horizon
          (oldScheduler) (failureProfile setup.program) oldSite oldOwing history
      have phaseAll (history : (M).InformationHistory who site.1)
          (supported : history ∈ phaseBelief.support) :
          PhaseOwesFailure setup leaks (failureProfile setup.program) who history.1.state := by
        have projected : projection history.1.state ∈
            (phaseBelief.map (fun history => projection history.1.state)).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨history, supported, rfl⟩
        rw [stateLaw] at projected
        rw [phaseOwesFailure_eq_projected setup leaks (oldLeaks) (failureProfile setup.program) who]
        exact oldAll _ projected
      have actualPositive : 0 < (M).informationMass assessment.strategy who site := by
        rw [assembled]
        exact positive
      have beliefEq : assessment.belief who site = phaseBelief := by
        have normalized := (BehavioralAssessment.isBayesConsistentAt_iff (M) assessment who site
          ((menu setup leaks bounds).decisionInformationAntichain (initialLaw setup) horizon
            scheduler who site) actualPositive).mp (bayes who site actualPositive)
        simpa only [assembled] using normalized
      rw [BehavioralAssessment.continuationContext_value, expect_bind_of_finite, beliefEq]
      have fixed (history : (M).InformationHistory who site.1)
          (supported : history ∈ phaseBelief.support) :
          expect ((M).runBehavioralTerminalFrom
            ((menu setup leaks bounds).bounded (initialLaw setup) horizon
              scheduler).wellFoundedHistories
            (Profile.update (sig := (M).behavioralSignature) assessment.strategy who alternative)
            history.1) (fun final => phaseExclusionBase setup .sequential (runtime setup) leaks
              (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
                final.state who) = excludedPayoff who := by
        have owed : history.1.state.elim False fun control =>
            RecoveryDecoded (failureProfile setup.program)
              (ProtocolState.OwesFailure who setup.program) control.execution.application.current :=
          by
          have valid := phaseAll history supported
          cases current : history.1.state with
          | none => rw [current] at valid; exact valid.elim
          | some control => rw [current] at valid; exact valid
        exact phase_owesFailure_expected_payoff setup leaks
          (sequentialRuntimePhasePlan setup.program)
          (sequentialRuntimePhasePlan_singleton setup.program)
          (setup.initialLaw.map setup.eventInputs) horizon scheduler parameter utility
          excludedPayoff (menu setup leaks bounds) completes
          ((menu setup leaks bounds).bounded (initialLaw setup) horizon
            scheduler).wellFoundedHistories
          (Profile.update (sig := (M).behavioralSignature) assessment.strategy who alternative) who
          history.1 owed
      exact (expect_congr_on_support fixed).trans (expect_constant _ _)

end Vegas.SequentialPhase
