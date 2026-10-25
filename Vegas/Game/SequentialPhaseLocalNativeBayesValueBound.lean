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
/-- The original actual phase local value is within a native foreign-exit error
of its existing native debt-stopped comparison value, for every focal law.
Only the physical phase completion contract is used. -/
theorem component_localValue_sub_native_debt_stopped_le_foreign_exit
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
    (excludedPayoff : Player → ℝ)
    (nativeCertificate : ((application setup (oldLeaks)).protocol
      ((oldInitial).map RecoveryState.native) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
        (oldScheduler))).WellFoundedHistories)
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
    ∃ (oldSite : (R).InformationSite who)
      (oldPositive : 0 < (R).informationMass oldProfile who oldSite),
      oldSite.1 = projectInfo site.1 ∧
      let oldBelief := (R).bayesBelief oldProfile who oldSite
        ((oldMenu).decisionInformationAntichain (oldInitial) horizon (oldScheduler) who oldSite)
        oldPositive
      let nativeStopped := (oldBelief.map Subtype.val).bind
        (RecoveryOnePacket.nativeDebtStoppedLaw setup (oldLeaks) bounds horizon (oldScheduler)
          nativeCertificate oldUpdated who)
      |localValue (2 * horizon + 1) (fun final => final.state)
          (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
          phaseAssessment site law -
        expect oldBelief (fun history => RecoveryOnePacket.nativeDebtStoppedValue setup (oldLeaks)
          bounds horizon (oldScheduler) parameter utility excludedPayoff nativeCertificate
          oldUpdated
          who history.1)| ≤
        (2 * bound) * (nativeStopped.toOuterMeasure
          {label | ForeignExclusionLabel who label}).toReal := by
  intro oldProfile agent agentClear oldUpdated
  obtain ⟨oldSite, oldPositive, inputEq, near⟩ :=
    component_localValue_sub_stopped_le_foreign_exit setup leaks bounds horizon scheduler fallback
      assessment scale positiveScale le_one weights who site past view siteInput clear positive law
      phaseAssessment assembled bayes parameter utility excludedPayoff
      (failureProfile setup.program)
      completes nonnegativeBound payoffBounded excludedBounded
  refine ⟨oldSite, oldPositive, inputEq, ?_⟩
  intro oldBelief nativeStopped
  let kernel := (R).runBehavioralUntil
    ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories oldUpdated
    (fun history => ¬ oldClear history.state ∨
      RecoveryDecodedState (leaks := oldLeaks) (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state)
  have controlled : ∀ history ∈ (oldBelief.map Subtype.val).support,
      ∃ current : (A).Control,
        history.state = some current ∧ current.execution.application.excluded = ∅ := by
    intro history supported
    obtain ⟨original, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    apply recovery_informationHistory_controlled_of_projected_clear setup leaks bounds horizon
      scheduler who past view clear oldSite
    · exact inputEq.trans (congrArg (PhaseRecoveryProjection.information (runtime setup) leaks
        (oldLeaks)) siteInput)
  let sourceInitial := (Vegas.initialLaw setup).map
    (fun native => (⟨native, ∅⟩ : RecoveryState (graph setup)))
  let : Fintype ((oldMenu).protocol sourceInitial horizon (oldScheduler)).History := by
    have nature : (A).FiniteNature sourceInitial (oldScheduler) :=
      recoveryNature setup leaks scheduler
    exact @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (oldMenu) sourceInitial
      horizon (oldScheduler) inferInstance nature
  have bridge := RecoveryOnePacket.debt_stopped_belief_eq_native_and_foreign_mass_le setup
    (oldLeaks) bounds horizon (oldScheduler) parameter utility excludedPayoff nativeCertificate
    ((A).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories
    ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories
    oldUpdated who (oldBelief.map Subtype.val) controlled
  have stoppedEq : (oldBelief.bind (fun history => (kernel history.1).map History.state)) =
      (((oldBelief.map Subtype.val).bind kernel).map History.state) := by
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
