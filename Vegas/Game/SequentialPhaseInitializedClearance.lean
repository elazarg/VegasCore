/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseInitializedNativeProjection
import Vegas.Game.SequentialPhaseInitializedProjection
import GameTheory.Analysis.Protocol.BehavioralTerminalConvergence
import Vegas.Game.SequentialPhaseHonestLaw
import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.SequentialPhaseNativeComparison

/-! # Vanishing initialized physical exclusion for actual phase completions -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

private theorem flag_mass_le_of_withinTV_false {α : Type*} {error : ℝ}
    {first : PMF Bool} {second : PMF α}
    (close : PMF.WithinTV error first (second.map (fun _ => false))) :
    (first true).toReal ≤ error := by
  have estimate := close.apply true
  rw [pmf_map_fun_const] at estimate
  simpa only [PMF.pure_apply, Bool.true_eq_false, ↓reduceIte, ENNReal.toReal_zero, sub_zero,
    abs_of_nonneg ENNReal.toReal_nonneg] using estimate

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

local notation "M" => model setup leaks bounds horizon scheduler
local notation "MP" => ReactiveApplication.ResponseMenu.protocol (menu setup leaks bounds)
  (phaseInitialLaw setup) horizon scheduler
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := phaseApplication
  (runtime setup) leaks) (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)

omit [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler] in
open Classical in
private def exclusionFlag (state : (phaseApplication (runtime setup) leaks).ProtocolState) : Bool :=
  decide (¬ phaseClear state)

include opportunity inclusion timely completes in
/-- The initialized common phase strategy excludes an owner only within the
same retained honest-mass budget as its actual native projection. -/
theorem component_initialized_exclusion_mass_le
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ)
    (fallback : ∀ who, (M).Policy who) :
    (((((M).runBehavioral
      (componentStrategy setup leaks bounds horizon scheduler fallback (sequence n) (scale n)
        (positive n).le (le_one n) (weights n)) (2 * horizon + 1)).map
        (fun final => exclusionFlag setup leaks final.state)) true).toReal) ≤
      (min (Fintype.card Player) 1 * horizon : ℕ) * (1 - slotRetention (scale n)) := by
  classical
  have coupling := component_initialized_projection_withinTV setup leaks bounds horizon scheduler
    fallback (sequence n) (scale n) (positive n).le (le_one n) (weights n) (fun _ => false)
    (exclusionFlag setup leaks) (by intro history clear; simp [exclusionFlag, clear])
  have upper := flag_mass_le_of_withinTV_false coupling
  exact upper.trans
    (component_projection_initialized_failure_mass_le setup leaks bounds horizon scheduler
      opportunity inclusion timely completes wellFormed covers capacity sequence scale positive
      le_one weights n)

include opportunity inclusion timely completes in
/-- Every supported endpoint of an initialized limit of actual common phase
completion strategies has empty physical excluded set. -/
theorem initialized_limit_no_exclusion
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Filter.Tendsto scale Filter.atTop (nhds 0)) {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (fallback : ∀ who, (M).Policy who)
    (assessments : ℕ → (M).BehavioralAssessment)
    (assembled : ∀ n, (assessments n).strategy =
      componentStrategy setup leaks bounds horizon scheduler fallback (sourceSequence n) (scale n)
        (positive n).le (le_one n) (weights n))
    (limit : (M).BehavioralAssessment) (index : ℕ → ℕ) (increasing : StrictMono index)
    (converges : ∀ who (site : (M).InformationSite who),
      PMFConvergesPointwise (fun n => (assessments (index n)).strategy who site.1)
        (limit.strategy who site.1)) :
    ∀ final ∈ ((M).runBehavioral limit.strategy (2 * horizon + 1)).support,
      ∀ control, final.state = some control → control.execution.application.current.excluded = ∅ :=
        by
  classical
  let budget : ℝ := (min (Fintype.card Player) 1 * horizon : ℕ)
  have approximation (n : ℕ) :
      (((((M).runBehavioral (assessments n).strategy (2 * horizon + 1)).map
        (fun final => exclusionFlag setup leaks final.state)) true).toReal) ≤
        budget * (1 - slotRetention (scale n)) := by
    rw [assembled n]
    exact component_initialized_exclusion_mass_le setup leaks bounds horizon scheduler opportunity
      inclusion timely completes wellFormed covers capacity sourceSequence scale positive le_one
      weights n fallback
  let certificate := ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
    scheduler).wellFoundedHistories
  have evaluation (profile : ∀ who, (M).BehavioralPolicy who) :
      (M).runBehavioralTerminalFrom certificate profile (MP).initHistory =
        (M).runBehavioral profile (2 * horizon + 1) :=
    (M).runBehavioralTerminalFrom_initHistory certificate profile
      ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon scheduler)
  have terminalConverges := (M).runBehavioralTerminalFrom_convergesPointwise certificate
    converges (MP).initHistory
  have runConverges : PMFConvergesPointwise
      (fun n => (M).runBehavioral (assessments (index n)).strategy (2 * horizon + 1))
      ((M).runBehavioral limit.strategy (2 * horizon + 1)) := by
    simpa only [evaluation] using terminalConverges
  have atomConverges :=
    (runConverges.map (fun final => exclusionFlag setup leaks final.state)).toReal true
  have retained := tendsto_slotRetention (vanishes.comp increasing.tendsto_atTop)
  have negligible : Filter.Tendsto
      (fun n => budget * (1 - slotRetention (scale (index n)))) Filter.atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub retained).const_mul budget
  have atomVanishes := squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => approximation (index n)) negligible
  have zero := tendsto_nhds_unique atomConverges atomVanishes
  have absent := pmf_toReal_eq_zero_iff.mp zero
  intro final supported control current
  by_contra excluded
  apply absent
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨final, supported, by simp [exclusionFlag, current, ReactiveApplication.stateInvariant,
    excluded]⟩

end Vegas.SequentialPhase
