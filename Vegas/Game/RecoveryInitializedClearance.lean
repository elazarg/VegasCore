/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryInitializedProjection
import GameTheory.Analysis.Protocol.BehavioralTerminalConvergence

/-! # No exclusion in limits of the actual initialized recovery completion

The exclusion flag is a runtime-state observation. Its mass is controlled by
the existing first-exclusion coupling and honest-retention bound, independently
of utility, count charges, or equality of a final payoff law.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon NativeScheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

private def exclusionFlag
    (state : (recoveryApplication (runtime setup) leaks).ProtocolState) : Bool :=
  state.elim false fun control => decide (control.execution.application.excluded ≠ ∅)

private theorem initialized_exclusion_mass_le_native_failure
    (profile : ∀ who, (R).BehavioralPolicy who) :
    (((((R).runBehavioral profile (2 * horizon + 1)).map
      (fun final => exclusionFlag setup leaks final.state)) true).toReal) ≤
      (((N).runBehavioral (sourceNativeProfile setup leaks bounds horizon scheduler profile)
        (2 * horizon + 1)).toOuterMeasure {history | ¬ Clear history.state}).toReal := by
  classical
  have close := recovery_initialized_projection_withinTV setup leaks bounds horizon scheduler
    profile (fun _ => false) (exclusionFlag setup leaks) (by
      intro state clear
      cases state with
      | none => rfl
      | some control => simp [exclusionFlag, clear control rfl])
  simpa [PMF.map_const, PMF.pure_apply, abs_of_nonneg ENNReal.toReal_nonneg] using
    close.apply true

variable [Fintype ((ReactiveApplication.ResponseMenu.protocol
    (Recovery.onePacketMenu (runtime setup) leaks bounds)
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler)).History]
  [(application setup leaks).FiniteNature (initialLaw setup)
    (nativeScheduler (runtime setup) leaks scheduler)]
  [∀ who, DecidableEq ((model setup leaks bounds
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler).InfoState who)]

/-- The actual common completion's initialized limit has no excluded owner on
its support. Only strategy convergence, honest retention, and the original
runtime service hypotheses are used; no payoff or count-law premise occurs. -/
theorem initialized_limit_no_exclusion
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0)) {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p))
    (fallback : ∀ who, (R).Policy who)
    (assessments : ℕ → (R).BehavioralAssessment)
    (assembled : ∀ n, (assessments n).strategy =
      (R).agentBehavior (R).playedInformation fallback
        (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
          (component setup leaks bounds Initial horizon scheduler (sourceSequence n) (scale n)
            (positive n).le (le_one n) agent)))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (limit : (R).BehavioralAssessment) (index : ℕ → ℕ) (increasing : StrictMono index)
    (converges : ∀ who (site : (R).InformationSite who),
      PMFConvergesPointwise (fun n => (assessments (index n)).strategy who site.1)
        (limit.strategy who site.1)) :
    ∀ final ∈ ((R).runBehavioral limit.strategy (2 * horizon + 1)).support,
      ∀ control, final.state = some control → control.execution.application.excluded = ∅ := by
  classical
  let budget : ℝ := (Fintype.card Player * (2 * horizon + 1) : ℕ)
  have approximation (n : ℕ) :
      (((((R).runBehavioral (assessments n).strategy (2 * horizon + 1)).map
        (fun final => exclusionFlag setup leaks final.state)) true).toReal) ≤
        budget * (1 - slotRetention (scale n)) := by
    exact (initialized_exclusion_mass_le_native_failure setup leaks bounds horizon scheduler
      (assessments n).strategy).trans
      (sourceNativeProfile_initialized_failure_mass_le setup leaks bounds horizon scheduler
        wellFormed covers capacity sourceSequence scale positive le_one weights n fallback
          (assessments n).strategy (assembled n) opportunity inclusion timely completes)
  let certificate := ((RMenu).bounded Initial horizon scheduler).wellFoundedHistories
  have evaluation (profile : ∀ who, (R).BehavioralPolicy who) :
      (R).runBehavioralTerminalFrom certificate profile (RP).initHistory =
        (R).runBehavioral profile (2 * horizon + 1) :=
    (R).runBehavioralTerminalFrom_initHistory certificate profile
      ((RMenu).bounded Initial horizon scheduler)
  have terminalConverges := (R).runBehavioralTerminalFrom_convergesPointwise certificate
    converges (RP).initHistory
  have runConverges : PMFConvergesPointwise
      (fun n => (R).runBehavioral (assessments (index n)).strategy (2 * horizon + 1))
      ((R).runBehavioral limit.strategy (2 * horizon + 1)) := by
    simpa only [evaluation] using terminalConverges
  have atomConverges :=
    (runConverges.map (fun final => exclusionFlag setup leaks final.state)).toReal true
  have retained := tendsto_slotRetention (vanishes.comp increasing.tendsto_atTop)
  have negligible : Tendsto (fun n => budget * (1 - slotRetention (scale (index n))))
      atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub retained).const_mul budget
  have atomVanishes := squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => approximation (index n)) negligible
  have zero := tendsto_nhds_unique atomConverges atomVanishes
  have absent := pmf_toReal_eq_zero_iff.mp zero
  intro final supported control current
  by_contra excluded
  apply absent
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨final, supported, by simp [exclusionFlag, current, excluded]⟩

end Vegas.RecoveryOnePacket
