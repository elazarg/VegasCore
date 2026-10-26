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

/-- Owed source debt at the actual projected input fixes the phase continuation
value for every whole policy, including policies reading future archived data. -/
theorem component_owing_continuation_value_eq
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
    (alternative : (M).BehavioralPolicy who) :
    (assessment.continuationContext
      ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
      site (fun final => phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          final.state who)).value alternative = excludedPayoff who := by
  classical
  cases input : site.1 with
  | none => rw [input] at siteClear; exact siteClear.elim
  | some data =>
      rcases data with ⟨past, view⟩
      have viewClear : view.application.2.excluded = ∅ := by
        rw [input] at siteClear
        exact siteClear
      obtain ⟨recoverySite, recoveryPositive, recoveryInput, stateLaw⟩ :=
          component_comparison_bayes_state_eq setup runtime
        leaks bounds horizon scheduler fallback source scale positiveScale le_one weights who site
        past view input viewClear positive
      let recoveryProfile := recoveryComparisonStrategy setup runtime leaks bounds horizon
        scheduler source
          scale
        positiveScale.le le_one weights
      let phaseProfile := componentStrategy setup runtime leaks bounds horizon scheduler fallback
        source
        scale positiveScale.le le_one weights
      let phaseBelief := (M).bayesBelief phaseProfile who site
        ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
          horizon
            scheduler
          who site) positive
      let recoveryBelief := (R).bayesBelief recoveryProfile who recoverySite
        ((RecoveryMenu).decisionInformationAntichain (RecoveryPrior) horizon (RecoveryScheduler) who
            recoverySite)
        recoveryPositive
      have sameAgent : (R).agentAt recoverySite =
          projectedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) siteClear
            := by
        apply congrArg (Sigma.mk who)
        apply Subtype.ext
        exact recoveryInput
      have recoveryOwing : RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks)
        bounds (RecoveryPrior)
          horizon
          (RecoveryScheduler) ((R).agentAt recoverySite) := sameAgent.symm ▸ owing
      have recoveryDebtSupported (state : (A).ProtocolState)
          (supported : state ∈ (recoveryBelief.map (fun history => history.1.state)).support) :
          RecoveryDecodedState (runtime := runtime) (leaks := RecoveryLeaks) (failureProfile
            setup.program)
            (ProtocolState.OwesFailure who setup.program) state := by
        obtain ⟨history, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        exact RecoveryOnePacket.owingAgent_allHistories (runtime := runtime) setup (RecoveryLeaks)
          bounds horizon
          (RecoveryScheduler) (failureProfile setup.program) recoverySite recoveryOwing history
      have phaseAll (history : (M).InformationHistory who site.1)
          (supported : history ∈ phaseBelief.support) :
          PhaseOwesFailure setup runtime leaks (failureProfile setup.program) who history.1.state
            := by
        have projected : projection history.1.state ∈
            (phaseBelief.map (fun history => projection history.1.state)).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨history, supported, rfl⟩
        rw [stateLaw] at projected
        rw [phaseOwesFailure_eq_projected setup runtime leaks (RecoveryLeaks) (failureProfile
          setup.program)
            who]
        exact recoveryDebtSupported _ projected
      have actualPositive : 0 < (M).informationMass assessment.strategy who site := by
        rw [assembled]
        exact positive
      have beliefEq : assessment.belief who site = phaseBelief := by
        have normalized := (BehavioralAssessment.isBayesConsistentAt_iff (M) assessment who site
          ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
            horizon
            scheduler who site) actualPositive).mp (bayes who site actualPositive)
        simpa only [assembled] using normalized
      rw [BehavioralAssessment.continuationContext_value, expect_bind_of_finite, beliefEq]
      have fixed (history : (M).InformationHistory who site.1)
          (supported : history ∈ phaseBelief.support) :
          expect ((M).runBehavioralTerminalFrom
            ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
              scheduler).wellFoundedHistories
            (Profile.update (sig := (M).behavioralSignature) assessment.strategy who alternative)
            history.1) (fun final => phaseExclusionBase setup .sequential runtime leaks
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
        exact phase_owesFailure_expected_payoff setup runtime leaks
          (sequentialRuntimePhasePlan setup.program)
          (sequentialRuntimePhasePlan_singleton setup.program)
          (setup.initialLaw.map setup.eventInputs) horizon scheduler parameter utility
          excludedPayoff (menu setup runtime leaks bounds) completes
          ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
            scheduler).wellFoundedHistories
          (Profile.update (sig := (M).behavioralSignature) assessment.strategy who alternative) who
          history.1 owed
      exact (expect_congr_on_support fixed).trans (expect_constant _ _)

end Vegas.SequentialPhase
