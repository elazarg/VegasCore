/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalNativeStoppedPayoff

/-! # Original local phase utility compared with native debt-stopped utility -/

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
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "RecoveryClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

variable (fallback : ∀ who, (model setup runtime leaks bounds horizon scheduler).Policy who)
  (assessment : setup.intendedModel.BehavioralAssessment)
  {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
  (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))

local notation "phaseProfile" => componentStrategy setup runtime leaks bounds horizon scheduler
  fallback
  assessment scale nonnegative le_one weights
local notation "comparison" => recoveryComparisonStrategy setup runtime leaks bounds horizon
  scheduler
  assessment scale nonnegative le_one weights
local notation "decoded" => fun who => SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program
  runtime leaks (menu setup runtime leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon
  scheduler who ((phaseProfile) who)
local notation "embedded" => fun who =>
  ReactiveApplication.ResponseMenu.embedPolicy (RecoveryMenu) (RecoveryPrior) horizon
      (RecoveryScheduler)
  who ((comparison) who)

variable (agent : (model setup runtime leaks bounds horizon scheduler).InformationAgent
    (model setup runtime leaks bounds horizon scheduler).playedInformation)
  (siteClear : ClearInput setup runtime leaks agent.2.1)
  (law : PMF ((model setup runtime leaks bounds horizon scheduler).Choice agent.1 agent.2.1))

local notation "phaseUpdated" => Profile.update (sig := InformationModel.behavioralSignature
  (model setup runtime leaks bounds horizon scheduler)) (phaseProfile) (Sigma.fst agent)
  (BehavioralPolicy.withLaw ((phaseProfile) (Sigma.fst agent)) (Subtype.val (Sigma.snd agent)) law)
local notation "RecoveryUpdated" => Profile.update (sig := InformationModel.behavioralSignature
  (recoveryModel setup runtime leaks bounds horizon scheduler)) (comparison) (Sigma.fst agent)
  (BehavioralPolicy.withLaw ((comparison) (Sigma.fst agent))
    (PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks)
      (Subtype.val (Sigma.snd agent)))
    (PMF.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent siteClear) law))
local notation "decodedUpdated" => fun who => SequentialPhaseRecoveryPolicy.behavioralPolicy
  setup.program runtime leaks (menu setup runtime leaks bounds)
  (setup.initialLaw.map setup.eventInputs) horizon scheduler who ((phaseUpdated) who)
local notation "embeddedUpdated" => fun who =>
  ReactiveApplication.ResponseMenu.embedPolicy (RecoveryMenu) (RecoveryPrior) horizon
      (RecoveryScheduler)
    who ((RecoveryUpdated) who)

open Classical in
/-- The actual original local phase continuation differs from the existing native
debt-stopped value only by foreign physical exclusion before focal source debt.
Completion is required solely for the original phase runtime. -/
theorem component_local_terminal_sub_native_debt_stopped_le_foreign_exit
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
          history.state agent.1| ≤ bound)
    (excludedBounded : |excludedPayoff agent.1| ≤ bound)
    (first : ((menu setup runtime leaks bounds).protocol (phaseInitialLaw setup) horizon
      scheduler).History)
    (second : (RecoveryProtocol).History) (same : projection first.state = second.state)
    (current : (A).Control) (state : second.state = some current)
    (empty : current.execution.application.excluded = ∅) :
    let stopped := (M).runBehavioralUntil
      ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
      (phaseUpdated) (fun history => PhaseDebtStopped setup runtime leaks (failureProfile
        setup.program)
        agent.1 history.state) first
    |expect ((M).runBehavioralTerminalFrom
        ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
        (phaseUpdated) first)
        (fun final => phaseExclusionBase setup .sequential runtime leaks
          (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
            final.state agent.1) -
      RecoveryOnePacket.nativeDebtStoppedValue (runtime := runtime) setup (RecoveryLeaks) bounds
        horizon
          (RecoveryScheduler)
        parameter utility excludedPayoff nativeCertificate (RecoveryUpdated) agent.1 second| ≤
      (2 * bound) * (stopped.toOuterMeasure {history |
        PhaseDebtStopped setup runtime leaks (failureProfile setup.program) agent.1 history.state ∧
        ¬ PhaseExcluded setup .sequential runtime leaks agent.1 history.state ∧
        ¬ PhaseOwesFailure setup runtime leaks (failureProfile setup.program) agent.1
          history.state}).toReal := by
  intro stopped
  have estimate := phase_expect_sub_debt_stopped_le_foreign_exit setup runtime leaks
    (sequentialRuntimePhasePlan setup.program) (sequentialRuntimePhasePlan_singleton setup.program)
    (setup.initialLaw.map setup.eventInputs) horizon scheduler parameter utility excludedPayoff
    (failureProfile setup.program) (menu setup runtime leaks bounds) completes
    ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
    (phaseUpdated) agent.1 nonnegativeBound payoffBounded excludedBounded first
  have readout := component_local_debt_stopped_expect_eq_native setup runtime leaks bounds horizon
    scheduler
    fallback assessment scale nonnegative le_one weights agent siteClear law parameter utility
    excludedPayoff nativeCertificate first second same current state empty
  rw [← readout]
  exact estimate

end Vegas.SequentialPhase
