/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalValueBound
import Vegas.Game.RecoveryDebtStoppedBelief
import Vegas.Game.SequentialPhaseRecoverySiteClear

/-! # Original local phase values and native debt-stopped foreign error -/

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
/-- The original actual phase local value is within a native foreign-exit error
of its existing native debt-stopped comparison value, for every focal law.
Only the physical phase completion contract is used. -/
theorem component_localValue_sub_native_debt_stopped_le_foreign_exit
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
    (excludedPayoff : Player → ℝ)
    (nativeCertificate : ((application (runtime := runtime) setup (RecoveryLeaks)).protocol
      ((RecoveryPrior).map RecoveryState.native) horizon
      (RecoveryProjection.nativeScheduler runtime (RecoveryLeaks)
        (RecoveryScheduler))).WellFoundedHistories)
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
    ∃ (recoverySite : (R).InformationSite who)
      (recoveryPositive : 0 < (R).informationMass recoveryProfile who recoverySite),
      recoverySite.1 = projectInfo site.1 ∧
      let recoveryBelief := (R).bayesBelief recoveryProfile who recoverySite
        ((RecoveryMenu).decisionInformationAntichain (RecoveryPrior) horizon (RecoveryScheduler) who
            recoverySite)
        recoveryPositive
      let nativeStopped := (recoveryBelief.map Subtype.val).bind
        (RecoveryOnePacket.nativeDebtStoppedLaw (runtime := runtime) setup (RecoveryLeaks) bounds
          horizon
            (RecoveryScheduler)
          nativeCertificate recoveryUpdated who)
      |localValue (2 * horizon + 1) (fun final => final.state)
          (phaseExclusionBase setup .sequential runtime leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
          phaseAssessment site law -
        expect recoveryBelief (fun history => RecoveryOnePacket.nativeDebtStoppedValue (runtime :=
          runtime) setup
            (RecoveryLeaks)
          bounds horizon (RecoveryScheduler) parameter utility excludedPayoff nativeCertificate
          recoveryUpdated
          who history.1)| ≤
        (2 * bound) * (nativeStopped.toOuterMeasure
          {label | ForeignExclusionLabel who label}).toReal := by
  intro recoveryProfile agent agentClear recoveryUpdated
  obtain ⟨recoverySite, recoveryPositive, inputEq, near⟩ :=
    component_localValue_sub_stopped_le_foreign_exit setup runtime leaks bounds horizon scheduler
      fallback
      assessment scale positiveScale le_one weights who site past view siteInput clear positive law
      phaseAssessment assembled bayes parameter utility excludedPayoff
      (failureProfile setup.program)
      completes nonnegativeBound payoffBounded excludedBounded
  refine ⟨recoverySite, recoveryPositive, inputEq, ?_⟩
  intro recoveryBelief nativeStopped
  let kernel := (R).runBehavioralUntil
    ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
        recoveryUpdated
    (fun history => ¬ RecoveryClear history.state ∨
      RecoveryDecodedState (runtime := runtime) (leaks := RecoveryLeaks) (failureProfile
        setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state)
  have controlled : ∀ history ∈ (recoveryBelief.map Subtype.val).support,
      ∃ current : (A).Control,
        history.state = some current ∧ current.execution.application.excluded = ∅ := by
    intro history supported
    obtain ⟨original, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    apply recovery_informationHistory_controlled_of_projected_clear setup runtime leaks bounds
      horizon
      scheduler who past view clear recoverySite
    · exact inputEq.trans (congrArg (PhaseRecoveryProjection.information runtime leaks
        (RecoveryLeaks)) siteInput)
  let sourceInitial := (Vegas.initialLaw setup).map
    (fun native => (⟨native, ∅⟩ : RecoveryState (graph setup)))
  let : Fintype ((RecoveryMenu).protocol sourceInitial horizon (RecoveryScheduler)).History := by
    have nature : (A).FiniteNature sourceInitial (RecoveryScheduler) :=
      recoveryNature setup runtime leaks scheduler
    exact @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (RecoveryMenu) sourceInitial
      horizon (RecoveryScheduler) inferInstance nature
  have bridge := RecoveryOnePacket.debt_stopped_belief_eq_native_and_foreign_mass_le (runtime :=
    runtime) setup
    (RecoveryLeaks) bounds horizon (RecoveryScheduler) parameter utility excludedPayoff
        nativeCertificate
    ((A).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
    ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
    recoveryUpdated who (recoveryBelief.map Subtype.val) controlled
  have stoppedEq : (recoveryBelief.bind (fun history => (kernel history.1).map History.state)) =
      (((recoveryBelief.map Subtype.val).bind kernel).map History.state) := by
    rw [PMF.bind_map, PMF.map_bind]
    rfl
  dsimp only at near
  rw [stoppedEq, expect_map, PMF.toOuterMeasure_map_apply] at near
  dsimp only [Function.comp_def] at near
  have readout := bridge.1
  simp only [expect_map, Function.comp_def] at readout
  erw [readout] at near
  exact near.trans (mul_le_mul_of_nonneg_left bridge.2 (by positivity))

end Vegas.SequentialPhase
