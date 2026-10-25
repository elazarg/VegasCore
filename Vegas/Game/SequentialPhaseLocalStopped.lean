/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalPolicy
import Vegas.Game.SequentialPhaseStoppedLaw
import Vegas.Game.SequentialPhaseBayesState
import Interaction.ReactiveLocalContinuation

/-! # Local phase law replacements and actual bounded recovery stopped laws -/

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

/-- Replacing the focal law at a clear phase site and using its exact recovery menu
image preserves the actual full one-step physical law at every clear history. -/
theorem component_local_comparison_run_one_map_state
    (first : ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History)
    (second : (RecoveryProtocol).History) (same : projection first.state = second.state)
    (clear : phaseClear first.state) :
    ((M).runBehavioralFrom (phaseUpdated) 1 first).map
        (fun history => projection history.state) =
      ((R).runBehavioralFrom (RecoveryUpdated) 1 second).map History.state := by
  let rawSecond := (RecoveryMenu).toRawHistory (RecoveryPrior) horizon (RecoveryScheduler) second
  have recoveryClearAt : RecoveryClear second.state := by
    rw [← same]
    cases stateEq : first.state <;> rw [stateEq] at clear <;> exact clear
  have callbacks : ∀ who,
      (embeddedUpdated) who ((rawModel).infoOf who rawSecond.trace) =
        (decodedUpdated) who ((rawModel).infoOf who rawSecond.trace) := by
    intro who
    have observed : (rawModel).infoOf who rawSecond.trace = (A).observe who second.state :=
      (A).info (RecoveryPrior) horizon (RecoveryScheduler) who rawSecond.trace
    rw [observed]
    by_cases equal : who = agent.1
    · subst who
      simp only [Profile.update_same]
      exact comparisonPolicy_withLaw_history setup leaks bounds horizon scheduler fallback
        assessment scale nonnegative le_one weights agent siteClear law first second same clear
    · simp only [Profile.update, Function.update_of_ne equal]
      exact comparisonPolicy_history setup leaks bounds horizon scheduler fallback assessment scale
        nonnegative le_one weights second recoveryClearAt who
  have rawOne : (rawModel).runBehavioralFrom (embeddedUpdated) 1 rawSecond =
      (rawModel).runBehavioralFrom (decodedUpdated) 1 rawSecond := by
    by_cases ended : (rawProtocol).terminal rawSecond.state
    · rw [(rawModel).runBehavioralFrom_of_terminal (h := rawSecond) _ _ ended,
        (rawModel).runBehavioralFrom_of_terminal (h := rawSecond) _ _ ended]
    · rw [(rawModel).runBehavioralFrom_succ_of_not_terminal (h := rawSecond) _ 0 ended,
        (rawModel).runBehavioralFrom_succ_of_not_terminal (h := rawSecond) _ 0 ended,
        (rawModel).behavioralJoint_congr rawSecond.trace ended callbacks]
      rfl
  have priorEq : (setup.initialLaw.map setup.eventInputs).map
      (fun input => (RecoveryState.mk (EventGraphRuntime.State.initial input) ∅ :
        RecoveryState (graph setup))) = RecoveryPrior := by
    simp only [recoveryInitialLaw, Vegas.initialLaw, serviceInitialLaw, PMF.map_comp,
      Function.comp_def]
  have producer := SequentialPhaseRecoveryPolicy.run_one_map_state_history setup.program
    (runtime setup) leaks (menu setup leaks bounds) bounds
    (PhaseCount.normalized_onePacket_included (runtime setup) leaks bounds)
    (setup.initialLaw.map setup.eventInputs) horizon scheduler
  erw [priorEq] at producer
  have phaseOne := producer (phaseUpdated) first rawSecond same clear
  have recoveryStep := congrArg (PMF.map History.state)
    ((RecoveryMenu).run_embed (RecoveryPrior) horizon (RecoveryScheduler) (RecoveryUpdated) 1
        second)
  rw [PMF.map_comp] at recoveryStep
  rw [rawOne] at recoveryStep
  exact phaseOne.trans recoveryStep.symm

/-- Arbitrary focal laws at a clear information site retain identical actual
physical stopped laws, including the first-exclusion endpoint. -/
theorem component_local_comparison_run_until_exclusion_or_guard_map_state
    (guard : (A).ProtocolState → Prop)
    (first : ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History)
    (second : (RecoveryProtocol).History) (same : projection first.state = second.state) :
    ((M).runBehavioralUntil
      ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
      (phaseUpdated)
      (fun history => ¬ phaseClear history.state ∨ guard (projection history.state)) first).map
        (fun history => projection history.state) =
      ((R).runBehavioralUntil
        ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
            (RecoveryUpdated)
        (fun history => ¬ RecoveryClear history.state ∨ guard history.state) second).map
          History.state := by
  classical
  apply (M).runBehavioralUntil_map_eq_of_step_maps (R)
    ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
        scheduler).wellFoundedHistories
    ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
    (phaseUpdated) (RecoveryUpdated)
    (fun history => ¬ phaseClear history.state ∨ guard (projection history.state))
    (fun history => ¬ RecoveryClear history.state ∨ guard history.state)
    (fun history => projection history.state) History.state ?_ ?_ first second same
  · intro first second matched
    have clearEq : phaseClear first.state ↔ RecoveryClear second.state := by
      rw [← matched]
      cases first.state <;> rfl
    have terminalEq :
        ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).terminal
          first.state ↔ (RecoveryProtocol).terminal second.state := by
      rw [← matched]
      cases first.state <;> rfl
    rw [clearEq, matched, terminalEq]
  · intro first second matched going _running
    exact component_local_comparison_run_one_map_state setup leaks bounds horizon scheduler
      fallback assessment scale nonnegative le_one weights agent siteClear law first second matched
        (not_not.mp (not_or.mp going).1)

end Vegas.SequentialPhase
