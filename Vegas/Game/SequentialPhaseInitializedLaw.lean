/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseInitializedNativeProjection
import Vegas.Game.SequentialPhaseInitializedProjection
import Vegas.Game.PhaseTerminalFailure
import Vegas.Game.SequentialPhaseHonestLaw
import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.SequentialPhaseNativeComparison

/-! # Initialized joint phase source readout and realized payoff laws -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : PhaseService.Opportunity (runtime setup) leaks (phaseInitialLaw setup) horizon
    scheduler delay)
  (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (phaseInitialLaw setup) horizon
    scheduler bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : PhaseService.CompletesPlay (runtime setup) leaks (phaseInitialLaw setup) horizon
    scheduler)

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup)
    (RecoveryLeaks)
  (recoveryScheduler setup leaks scheduler)
local notation "N" => onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
  (nativeScheduler)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)
local notation "NativeModel" => onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
  horizon (nativeScheduler)
local notation "NativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu (runtime setup) (RecoveryLeaks) bounds

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

include opportunity inclusion timely completes in
/-- The original phase joint typed readout and realized base-payoff law
approaches its source law. Arbitrary excluded suffixes cost only their rare mass. -/
theorem component_initialized_readout_withinTV
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ)
    (fallback : ∀ who, (model setup leaks bounds horizon scheduler).Policy who)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    PMF.WithinTV (2 * ((Fintype.card Player * (2 * horizon + 1) : ℕ) *
      (1 - slotRetention (scale n))))
      (((model setup leaks bounds horizon scheduler).runBehavioral
        (componentStrategy setup leaks bounds horizon scheduler fallback (sequence n) (scale n)
          (positive n).le (le_one n) (weights n)) (2 * horizon + 1)).map (fun final =>
        (phaseSourceReadout setup .sequential (runtime setup) leaks final.state,
          phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
            final.state)))
      ((setup.intendedModel.runBehavioral (sequence n).strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff)) := by
  classical
  have coupling := component_initialized_projection_withinTV setup leaks bounds horizon scheduler
    fallback (sequence n) (scale n) (positive n).le (le_one n) (weights n)
    (fun state => (sourceReadout setup (RecoveryLeaks) state,
      exclusionBase setup parameter utility excludedPayoff (RecoveryLeaks) state))
    (fun state => (phaseSourceReadout setup .sequential (runtime setup) leaks state,
      phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff state))
    (by
      intro history clear
      refine Prod.ext ?_ ?_
      · cases history.state <;> rfl
      · funext who
        cases state : history.state with
        | none => rfl
        | some control =>
          have empty : control.execution.application.current.excluded = ∅ := by
            simpa only [state, ReactiveApplication.stateInvariant] using clear
          have coverage := phaseFailureCoverage_history (runtime setup) leaks
            (sequentialRuntimePhasePlan setup.program) (setup.initialLaw.map setup.eventInputs)
            horizon scheduler
            (state ▸ (menu setup leaks bounds).toRawTrace (phaseInitialLaw setup) horizon scheduler
              history.trace)
          have physical := phaseExclusionBase_eq_recoveryExclusionBase setup leaks (RecoveryLeaks)
            parameter utility excludedPayoff control coverage who
          exact physical.trans (recoveryExclusionBase_of_not_excluded parameter utility
            excludedPayoff _ who (by
              change who ∉ control.execution.application.current.excluded
              rw [empty]
              exact Finset.notMem_empty who)))
  have bounded := coupling.mono
    (component_projection_initialized_failure_mass_le setup leaks bounds horizon scheduler
      opportunity inclusion timely completes wellFormed covers capacity sequence scale positive
      le_one weights n)
  have native := component_projection_initialized_readout_withinTV setup leaks bounds horizon
    scheduler opportunity inclusion timely completes wellFormed covers capacity sequence scale
    positive le_one weights n parameter utility excludedPayoff
  simpa only [two_mul] using bounded.trans native

end Vegas.SequentialPhase
