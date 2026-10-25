/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalStoppedPayoff
import Vegas.Game.RecoveryDebtStoppedReadout
import Vegas.Game.RecoveryValueTransport

/-! # Actual phase local stopped payoff equals native debt-stopped utility -/

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
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "RecoveryClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

variable (fallback : ∀ who, (model setup leaks bounds horizon scheduler).Policy who)
  (assessment : setup.intendedModel.BehavioralAssessment)
  {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
  (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))

local notation "phaseProfile" => componentStrategy setup leaks bounds horizon scheduler fallback
  assessment scale nonnegative le_one weights
local notation "comparison" => recoveryComparisonStrategy setup leaks bounds horizon scheduler
  assessment scale nonnegative le_one weights
local notation "decoded" => fun who => SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program
  (runtime setup) leaks (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon
  scheduler who ((phaseProfile) who)
local notation "embedded" => fun who =>
  ReactiveApplication.ResponseMenu.embedPolicy (RecoveryMenu) (RecoveryPrior) horizon
      (RecoveryScheduler)
  who ((comparison) who)

variable (agent : (model setup leaks bounds horizon scheduler).InformationAgent
    (model setup leaks bounds horizon scheduler).playedInformation)
  (siteClear : ClearInput setup leaks agent.2.1)
  (law : PMF ((model setup leaks bounds horizon scheduler).Choice agent.1 agent.2.1))

local notation "phaseUpdated" => Profile.update (sig := InformationModel.behavioralSignature
  (model setup leaks bounds horizon scheduler)) (phaseProfile) (Sigma.fst agent)
  (BehavioralPolicy.withLaw ((phaseProfile) (Sigma.fst agent)) (Subtype.val (Sigma.snd agent)) law)
local notation "RecoveryUpdated" => Profile.update (sig := InformationModel.behavioralSignature
  (recoveryModel setup leaks bounds horizon scheduler)) (comparison) (Sigma.fst agent)
  (BehavioralPolicy.withLaw ((comparison) (Sigma.fst agent))
    (PhaseRecoveryProjection.information (runtime setup) leaks (RecoveryLeaks)
      (Subtype.val (Sigma.snd agent)))
    (PMF.map (choiceEquiv setup leaks bounds horizon scheduler agent siteClear) law))
local notation "decodedUpdated" => fun who => SequentialPhaseRecoveryPolicy.behavioralPolicy
  setup.program (runtime setup) leaks (menu setup leaks bounds)
  (setup.initialLaw.map setup.eventInputs) horizon scheduler who ((phaseUpdated) who)
local notation "embeddedUpdated" => fun who =>
  ReactiveApplication.ResponseMenu.embedPolicy (RecoveryMenu) (RecoveryPrior) horizon
      (RecoveryScheduler)
    who ((RecoveryUpdated) who)

open Classical in
/-- The original local phase stopped payoff equals the existing actual native
debt-stopped value of its bounded comparison, without any recovery service
or completion contract. -/
theorem component_local_debt_stopped_expect_eq_native
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (nativeCertificate : ((application setup (RecoveryLeaks)).protocol
      ((RecoveryPrior).map RecoveryState.native) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) (RecoveryLeaks)
        (RecoveryScheduler))).WellFoundedHistories)
    (first : ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History)
    (second : (RecoveryProtocol).History) (same : projection first.state = second.state)
    (current : (A).Control) (state : second.state = some current)
    (empty : current.execution.application.excluded = ∅) :
    expect ((M).runBehavioralUntil
      ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
      (phaseUpdated)
      (fun history => PhaseDebtStopped setup leaks (failureProfile setup.program) agent.1
        history.state) first)
      (fun history => phaseDebtStoppedPayoff setup leaks parameter utility excludedPayoff
        (failureProfile setup.program) agent.1 history.state) =
      RecoveryOnePacket.nativeDebtStoppedValue setup (RecoveryLeaks) bounds horizon
          (RecoveryScheduler)
        parameter utility excludedPayoff nativeCertificate (RecoveryUpdated) agent.1 second := by
  have physical := component_local_debt_stopped_expect_eq_recovery setup leaks bounds horizon
    scheduler fallback assessment scale nonnegative le_one weights agent siteClear law parameter
    utility excludedPayoff (failureProfile setup.program) first second same
  have native := recovery_debt_stopped_expect_eq_native parameter utility excludedPayoff
    (failureProfile setup.program) (RecoveryPrior) (RecoveryOnePacket.initialLaw_initialized setup)
    horizon (RecoveryScheduler) (RecoveryMenu) nativeCertificate
    ((A).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
    ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
    (RecoveryUpdated) agent.1 second current state empty
  have stopEq :
      (fun history : (RecoveryProtocol).History => ¬ RecoveryClear history.state ∨
        RecoveryDecodedState (leaks := RecoveryLeaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure agent.1 setup.program) history.state) =
      fun history => RecoveryPublicExclusion (setup := setup) (leaks := RecoveryLeaks) history.state
          ∨
        RecoveryDecodedState (leaks := RecoveryLeaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure agent.1 setup.program) history.state := by
    funext history
    cases history.state <;>
      simp only [ReactiveApplication.stateInvariant, RecoveryPublicExclusion,
        not_true_eq_false]
  rw [stopEq] at physical
  refine physical.trans ?_
  have clear : ∀ next, second.state = some next → next.execution.application.excluded = ∅ := by
    intro next found
    cases Option.some.inj (state.symm.trans found)
    exact empty
  unfold RecoveryOnePacket.nativeDebtStoppedValue RecoveryOnePacket.nativeDebtStoppedLaw
  rw [dite_eq_left clear]
  convert native using 1

end Vegas.SequentialPhase
