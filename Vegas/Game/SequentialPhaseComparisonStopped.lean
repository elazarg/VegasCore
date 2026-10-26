/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonPolicy
import Vegas.Game.SequentialPhaseStoppedLaw
import Vegas.Game.SequentialPhaseBayesState
import Interaction.ReactiveLocalContinuation

/-! # Actual bounded recovery comparison laws before exclusion -/

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

private theorem raw_decoded_run_one (history : (rawProtocol).History) :
    ((rawModel).runBehavioralFrom (decoded) 1 history).map History.state =
      (A).controlStep (RecoveryPrior) horizon (RecoveryScheduler)
        (fun who => SequentialPhaseRecoveryPolicy.policy setup.program runtime leaks
          ((menu setup runtime leaks bounds).decodeProfile (phaseInitialLaw setup) horizon scheduler
            (phaseProfile) who)) history.state := by
  let players := fun who => SequentialPhaseRecoveryPolicy.policy setup.program runtime
    leaks
    ((menu setup runtime leaks bounds).decodeProfile (phaseInitialLaw setup) horizon scheduler
      (phaseProfile) who)
  change ((rawModel).runBehavioralFrom (fun who => (A).encodePolicy (players who)) 1 history).map
    History.state = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (rawModel)
    ((A).singleMover (RecoveryPrior) horizon (RecoveryScheduler)), (A).run_map_state]
  simp only [Function.iterate_one, PMF.pure_bind]
  rfl

/-- The bounded global comparison and decoded phase policy have the same full
physical one-step law at every actual clear bounded history. -/
theorem comparison_run_one_map_state
    (first : (RecoveryProtocol).History) (second : (rawProtocol).History)
    (same : first.state = second.state) (clear : RecoveryClear first.state) :
    ((R).runBehavioralFrom (comparison) 1 first).map History.state =
      ((rawModel).runBehavioralFrom (decoded) 1 second).map History.state := by
  let rawFirst := (RecoveryMenu).toRawHistory (RecoveryPrior) horizon (RecoveryScheduler) first
  have localPolicies : ∀ who, (embedded) who ((rawModel).infoOf who rawFirst.trace) =
      (decoded) who ((rawModel).infoOf who rawFirst.trace) := by
    intro who
    have observed : (rawModel).infoOf who rawFirst.trace = (A).observe who first.state :=
      (A).info (RecoveryPrior) horizon (RecoveryScheduler) who rawFirst.trace
    rw [observed]
    exact comparisonPolicy_history setup runtime leaks bounds horizon scheduler fallback
      assessment scale
      nonnegative le_one weights first clear who
  have one : (rawModel).runBehavioralFrom (embedded) 1 rawFirst =
      (rawModel).runBehavioralFrom (decoded) 1 rawFirst := by
    by_cases ended : (rawProtocol).terminal rawFirst.state
    · rw [(rawModel).runBehavioralFrom_of_terminal (h := rawFirst) _ _ ended,
        (rawModel).runBehavioralFrom_of_terminal (h := rawFirst) _ _ ended]
    · rw [(rawModel).runBehavioralFrom_succ_of_not_terminal (h := rawFirst) _ 0 ended,
        (rawModel).runBehavioralFrom_succ_of_not_terminal (h := rawFirst) _ 0 ended,
        (rawModel).behavioralJoint_congr rawFirst.trace ended localPolicies]
      rfl
  calc
    _ = ((rawModel).runBehavioralFrom (embedded) 1 rawFirst).map History.state := by
      have law := congrArg (PMF.map History.state)
        ((RecoveryMenu).run_embed (RecoveryPrior) horizon (RecoveryScheduler) (comparison) 1 first)
      rw [PMF.map_comp] at law
      exact law
    _ = ((rawModel).runBehavioralFrom (decoded) 1 rawFirst).map History.state := by rw [one]
    _ = _ := by
      rw [raw_decoded_run_one, raw_decoded_run_one]
      exact congrArg _ same

/-- Equality holds until exclusion or an arbitrary physical guard. The two
policies need not agree after exclusion or at unplayed inputs. -/
theorem comparison_run_until_exclusion_or_guard_map_state
    (guard : (A).ProtocolState → Prop)
    (first : (RecoveryProtocol).History) (second : (rawProtocol).History)
    (same : first.state = second.state) :
    ((R).runBehavioralUntil
      ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
          (comparison)
      (fun history => ¬ RecoveryClear history.state ∨ guard history.state) first).map History.state
          =
    ((rawModel).runBehavioralUntil
      ((A).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories (decoded)
      (fun history => ¬ RecoveryClear history.state ∨ guard history.state) second).map
        History.state := by
  classical
  apply (R).runBehavioralUntil_map_eq_of_step_maps (rawModel)
    ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
    ((A).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
    (comparison) (decoded)
    (fun history => ¬ RecoveryClear history.state ∨ guard history.state)
    (fun history => ¬ RecoveryClear history.state ∨ guard history.state)
    History.state History.state ?_ ?_ first second same
  · intro first second matched
    rw [matched]
    rfl
  · intro first second matched going _running
    exact comparison_run_one_map_state setup runtime leaks bounds horizon scheduler fallback
      assessment
      scale nonnegative le_one weights first second matched (not_not.mp (not_or.mp going).1)

/-- The actual phase component assembly and actual recovery bounded comparison
have identical full physical stopped laws from every matched pair of histories. -/
theorem component_comparison_run_until_exclusion_or_guard_map_state
    (guard : (A).ProtocolState → Prop)
    (first : ((menu setup runtime leaks bounds).protocol (phaseInitialLaw setup) horizon
      scheduler).History)
    (second : (RecoveryProtocol).History) (same : projection first.state = second.state) :
    ((M).runBehavioralUntil
      ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
      (phaseProfile)
      (fun history => ¬ phaseClear history.state ∨ guard (projection history.state))
      first).map (fun history => projection history.state) =
    ((R).runBehavioralUntil
      ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
          (comparison)
      (fun history => ¬ RecoveryClear history.state ∨ guard history.state) second).map
        History.state := by
  have priorEq : (setup.initialLaw.map setup.eventInputs).map
      (fun input => (RecoveryState.mk (EventGraphRuntime.State.initial input) ∅ :
        RecoveryState (graph setup))) = RecoveryPrior := by
    simp only [recoveryInitialLaw, Vegas.initialLaw, serviceInitialLaw, PMF.map_comp,
      Function.comp_def]
  have phaseProducer := SequentialPhaseRecoveryPolicy.run_until_exclusion_or_guard_map_state
    setup.program runtime leaks (menu setup runtime leaks bounds) bounds
    (PhaseCount.normalized_onePacket_included runtime leaks bounds)
    (setup.initialLaw.map setup.eventInputs) horizon scheduler
    ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
        scheduler).wellFoundedHistories
  erw [priorEq] at phaseProducer
  have phaseLaw := phaseProducer
    ((A).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories guard
        (phaseProfile)
    first ((RecoveryMenu).toRawHistory (RecoveryPrior) horizon (RecoveryScheduler) second) same
  have recoveryLaw := comparison_run_until_exclusion_or_guard_map_state setup runtime leaks bounds
    horizon
    scheduler fallback assessment scale nonnegative le_one weights guard second
    ((RecoveryMenu).toRawHistory (RecoveryPrior) horizon (RecoveryScheduler) second) rfl
  exact phaseLaw.trans recoveryLaw.symm

end Vegas.SequentialPhase
