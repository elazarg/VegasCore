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

private theorem raw_decoded_run_one (history : (rawProtocol).History) :
    ((rawModel).runBehavioralFrom (decoded) 1 history).map History.state =
      (A).controlStep (oldInitial) horizon (oldScheduler)
        (fun who => SequentialPhaseRecoveryPolicy.policy setup.program (runtime setup) leaks
          ((menu setup leaks bounds).decodeProfile (initialLaw setup) horizon scheduler
            (phaseProfile) who)) history.state := by
  let players := fun who => SequentialPhaseRecoveryPolicy.policy setup.program (runtime setup)
    leaks
    ((menu setup leaks bounds).decodeProfile (initialLaw setup) horizon scheduler
      (phaseProfile) who)
  change ((rawModel).runBehavioralFrom (fun who => (A).encodePolicy (players who)) 1 history).map
    History.state = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (rawModel)
    ((A).singleMover (oldInitial) horizon (oldScheduler)), (A).run_map_state]
  simp only [Function.iterate_one, PMF.pure_bind]
  rfl

/-- The bounded global comparison and decoded phase policy have the same full
physical one-step law at every actual clear bounded history. -/
theorem comparison_run_one_map_state
    (first : (oldProtocol).History) (second : (rawProtocol).History)
    (same : first.state = second.state) (clear : oldClear first.state) :
    ((R).runBehavioralFrom (comparison) 1 first).map History.state =
      ((rawModel).runBehavioralFrom (decoded) 1 second).map History.state := by
  let rawFirst := (oldMenu).toRawHistory (oldInitial) horizon (oldScheduler) first
  have localPolicies : ∀ who, (embedded) who ((rawModel).infoOf who rawFirst.trace) =
      (decoded) who ((rawModel).infoOf who rawFirst.trace) := by
    intro who
    have observed : (rawModel).infoOf who rawFirst.trace = (A).observe who first.state :=
      (A).info (oldInitial) horizon (oldScheduler) who rawFirst.trace
    rw [observed]
    exact comparisonPolicy_history setup leaks bounds horizon scheduler fallback assessment scale
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
        ((oldMenu).run_embed (oldInitial) horizon (oldScheduler) (comparison) 1 first)
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
    (first : (oldProtocol).History) (second : (rawProtocol).History)
    (same : first.state = second.state) :
    ((R).runBehavioralUntil
      ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories (comparison)
      (fun history => ¬ oldClear history.state ∨ guard history.state) first).map History.state =
    ((rawModel).runBehavioralUntil
      ((A).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories (decoded)
      (fun history => ¬ oldClear history.state ∨ guard history.state) second).map
        History.state := by
  classical
  apply (R).runBehavioralUntil_map_eq_of_step_maps (rawModel)
    ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories
    ((A).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories
    (comparison) (decoded)
    (fun history => ¬ oldClear history.state ∨ guard history.state)
    (fun history => ¬ oldClear history.state ∨ guard history.state)
    History.state History.state ?_ ?_ first second same
  · intro first second matched
    rw [matched]
    rfl
  · intro first second matched going _running
    exact comparison_run_one_map_state setup leaks bounds horizon scheduler fallback assessment
      scale nonnegative le_one weights first second matched (not_not.mp (not_or.mp going).1)

/-- The actual phase component assembly and actual old bounded comparison
have identical full physical stopped laws from every matched pair of histories. -/
theorem component_comparison_run_until_exclusion_or_guard_map_state
    (guard : (A).ProtocolState → Prop)
    (first : ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History)
    (second : (oldProtocol).History) (same : projection first.state = second.state) :
    ((M).runBehavioralUntil
      ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
      (phaseProfile)
      (fun history => ¬ phaseClear history.state ∨ guard (projection history.state))
      first).map (fun history => projection history.state) =
    ((R).runBehavioralUntil
      ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories (comparison)
      (fun history => ¬ oldClear history.state ∨ guard history.state) second).map
        History.state := by
  have phaseLaw := SequentialPhaseRecoveryPolicy.run_until_exclusion_or_guard_map_state
    setup.program (runtime setup) leaks (menu setup leaks bounds) bounds
    (PhaseCount.normalized_onePacket_included (runtime setup) leaks bounds)
    (setup.initialLaw.map setup.eventInputs) horizon scheduler
    ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
    ((A).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories guard (phaseProfile)
    first ((oldMenu).toRawHistory (oldInitial) horizon (oldScheduler) second) same
  have oldLaw := comparison_run_until_exclusion_or_guard_map_state setup leaks bounds horizon
    scheduler fallback assessment scale nonnegative le_one weights guard second
    ((oldMenu).toRawHistory (oldInitial) horizon (oldScheduler) second) rfl
  exact phaseLaw.trans oldLaw.symm

end Vegas.SequentialPhase
