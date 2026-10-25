/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalStopped
import Vegas.Game.SequentialPhaseStoppedPayoffHistory

/-! # Exact original local stopped payoff correspondence -/

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
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "oldClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

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
  ReactiveApplication.ResponseMenu.embedPolicy (oldMenu) (oldInitial) horizon (oldScheduler)
  who ((comparison) who)

variable (agent : (model setup leaks bounds horizon scheduler).InformationAgent
    (model setup leaks bounds horizon scheduler).playedInformation)
  (siteClear : ClearInput setup leaks agent.2.1)
  (law : PMF ((model setup leaks bounds horizon scheduler).Choice agent.1 agent.2.1))

local notation "phaseUpdated" => Profile.update (sig := InformationModel.behavioralSignature
  (model setup leaks bounds horizon scheduler)) (phaseProfile) (Sigma.fst agent)
  (BehavioralPolicy.withLaw ((phaseProfile) (Sigma.fst agent)) (Subtype.val (Sigma.snd agent)) law)
local notation "oldUpdated" => Profile.update (sig := InformationModel.behavioralSignature
  (recoveryModel setup leaks bounds horizon scheduler)) (comparison) (Sigma.fst agent)
  (BehavioralPolicy.withLaw ((comparison) (Sigma.fst agent))
    (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)
      (Subtype.val (Sigma.snd agent)))
    (PMF.map (choiceEquiv setup leaks bounds horizon scheduler agent siteClear) law))
local notation "decodedUpdated" => fun who => SequentialPhaseRecoveryPolicy.behavioralPolicy
  setup.program (runtime setup) leaks (menu setup leaks bounds)
  (setup.initialLaw.map setup.eventInputs) horizon scheduler who ((phaseUpdated) who)
local notation "embeddedUpdated" => fun who =>
  ReactiveApplication.ResponseMenu.embedPolicy (oldMenu) (oldInitial) horizon (oldScheduler)
    who ((oldUpdated) who)

open Classical in
/-- Actual local phase and bounded recovery continuation laws give exactly the
same stopped payoff. The phase payoff is the original parameterized utility;
physical failure coverage is derived on every supported phase endpoint. -/
theorem component_local_debt_stopped_expect_eq_recovery
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program)
    (first : ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History)
    (second : (oldProtocol).History) (same : projection first.state = second.state) :
    expect ((M).runBehavioralUntil
      ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
      (phaseUpdated) (fun history => PhaseDebtStopped setup leaks source agent.1 history.state)
      first) (fun history => phaseDebtStoppedPayoff setup leaks parameter utility excludedPayoff
        source agent.1 history.state) =
      expect ((R).runBehavioralUntil
        ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories (oldUpdated)
        (fun history => ¬ oldClear history.state ∨
          RecoveryDecodedState (leaks := oldLeaks) source
            (ProtocolState.OwesFailure agent.1 setup.program) history.state) second)
        (fun history => if RecoveryPublicExclusion (setup := setup) (leaks := oldLeaks)
            history.state ∨ RecoveryDecodedState (leaks := oldLeaks) source
              (ProtocolState.OwesFailure agent.1 setup.program) history.state then
          excludedPayoff agent.1 else
          recoveryExclusionBase parameter utility excludedPayoff history.state agent.1) := by
  let guard := fun state : (A).ProtocolState => RecoveryDecodedState (leaks := oldLeaks) source
    (ProtocolState.OwesFailure agent.1 setup.program) state
  let read := fun state : (A).ProtocolState =>
    if RecoveryPublicExclusion (setup := setup) (leaks := oldLeaks) state ∨ guard state then
      excludedPayoff agent.1 else
      recoveryExclusionBase parameter utility excludedPayoff state agent.1
  have matchedLaw := component_local_comparison_run_until_exclusion_or_guard_map_state setup leaks
    bounds horizon scheduler fallback assessment scale nonnegative le_one weights agent siteClear
    law guard first second same
  have mapped := congrArg (fun law : PMF (A).ProtocolState => expect law read) matchedLaw
  simp only [expect_map, Function.comp_def] at mapped
  have stopEq : (fun history :
      ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History =>
        PhaseDebtStopped setup leaks source agent.1 history.state) =
      fun history => ¬ phaseClear history.state ∨ guard (projection history.state) := by
    funext history
    unfold PhaseDebtStopped
    rw [phaseOwesFailure_eq_projected setup leaks oldLeaks]
    rfl
  rw [stopEq]
  refine (expect_congr_on_support (fun history _supported => ?_)).trans mapped
  exact phaseDebtStoppedPayoff_history_eq_projected setup leaks oldLeaks
    (sequentialRuntimePhasePlan setup.program) (setup.initialLaw.map setup.eventInputs) horizon
    scheduler (menu setup leaks bounds) parameter utility excludedPayoff source agent.1 history

end Vegas.SequentialPhase
