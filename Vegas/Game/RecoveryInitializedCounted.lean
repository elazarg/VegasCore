/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComparisonRetention
import Vegas.Game.RecoveryNativeComparison
import Vegas.Game.RecoveryComparisonStopped
import Vegas.Game.OnePacketHonestTerminalApproximation

/-! # Initialized retention of actual recovery projections under counted native service -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (RecoveryProjection.nativeScheduler runtime leaks scheduler)
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon
    (RecoveryProjection.nativeScheduler runtime leaks scheduler)
local notation "RawN" => ReactiveApplication.information (application setup runtime leaks)
  (PMF.map RecoveryState.native Initial) horizon (RecoveryProjection.nativeScheduler runtime leaks
    scheduler)
local notation "RawR" => ReactiveApplication.information
  (recoveryApplication runtime leaks) Initial horizon scheduler
local notation "RawNP" => ReactiveApplication.protocol (application setup runtime leaks)
  (PMF.map RecoveryState.native Initial) horizon (RecoveryProjection.nativeScheduler runtime leaks
    scheduler)
local notation "RawRP" => ReactiveApplication.protocol
  (recoveryApplication runtime leaks) Initial horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

variable [Fintype ((ReactiveApplication.ResponseMenu.protocol (Recovery.onePacketMenu runtime
  leaks bounds) (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState
    (graph setup))) (initialLaw setup)) horizon scheduler)).History]
  [(application setup runtime leaks).FiniteNature (initialLaw setup) ((nativeScheduler runtime
    leaks scheduler))]
  [∀ who, DecidableEq (((model setup runtime leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler)).InfoState
    who)]
  (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
  (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
  (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
  (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
  {slots : Nat}
  (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler slots p)) (n : ℕ)
  (fallback : ∀ who, ((model setup runtime leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler)).Policy
    who) (strategy : ∀ who, ((model setup runtime leaks bounds (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).BehavioralPolicy who)
  (assembled : strategy = ((model setup runtime leaks bounds (PMF.map (fun native =>
    (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).agentBehavior ((model setup runtime leaks bounds (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).playedInformation fallback
    (fun agent => (weights n (pool setup runtime leaks bounds (PMF.map (fun native =>
      (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler agent)).bind
      (component setup runtime leaks bounds (PMF.map (fun native => (RecoveryState.mk native ∅ :
    RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler (sequence n) (scale n)
        (positive n).le (le_one n) agent)))
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon (RecoveryProjection.nativeScheduler
      runtime leaks scheduler)).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    OpportunityAt runtime leaks control.execution delay)
  (inclusion : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon (RecoveryProjection.nativeScheduler
      runtime leaks scheduler)).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    ProtectedInclusionAt runtime leaks control.execution bound)
  (timely : runtime.AsyncTimely delay bound)
  (completes : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon (RecoveryProjection.nativeScheduler
      runtime leaks scheduler)).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    (application setup runtime leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)
include wellFormed covers capacity opportunity inclusion timely completes assembled in
/-- Actual common recovery strategies under counted service retain initialized honest native play;
only the original completion weights are used. -/
theorem sourceNativeProfile_dominatesHonestFrom_initialized_of_counted_service
    (certificate : (NP).WellFoundedHistories) :
    DominatesHonestFrom setup runtime leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)
      (sequence n) (slotRetention (scale n))
      (sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy) (NP).initHistory
        := by
  classical
  have retained := OnePacketComparison.assembled_dominatesHonestFrom_initialized setup runtime leaks
    bounds horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler)
      wellFormed covers capacity sequence scale positive le_one
    (fun n => nativeComparisonWeights setup runtime leaks bounds horizon scheduler (weights n))
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights)
    (nativeComparisonSequence_assembled setup runtime leaks bounds horizon scheduler sequence
      scale positive
      le_one weights) n opportunity inclusion timely completes certificate
  intro fuel history reached who choice
  have lower := retained fuel history reached who choice
  change slotRetention (scale n) *
    ((honestProfile setup runtime leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) (sequence n)
      who ((N).infoOf who history.trace)) choice).toReal ≤
    ((nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one
      weights n who ((N).infoOf who history.trace)) choice).toReal at lower
  by_cases running : ¬ (NP).terminal history.state
  · have clear : Clear history.state := by
      cases current : history.state with
      | none => trivial
      | some control =>
        obtain ⟨point, decoded, intended⟩ := counted_honest_initialized_intended (runtime :=
          runtime) opportunity
          inclusion timely
          completes wellFormed covers capacity (sequence n) certificate fuel history reached control
            current
        exact exclusionEvidence_of_decodedIntended (runtime := runtime)
          ((NMenu).toRawTrace (initialLaw setup) horizon (RecoveryProjection.nativeScheduler
            runtime leaks scheduler)
            (current ▸ history.trace)) decoded intended
    have valid : ∀ control, history.state = some control →
        ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) := by
      intro control current
      rw [current] at clear
      exact clear
    rw [nativeComparisonStrategy_eq_projection_at_clear setup runtime leaks bounds horizon scheduler
      sequence scale positive le_one weights n fallback strategy assembled history.trace valid
        running who] at lower
    exact lower
  · have ended := not_not.mp running
    have inactive : ¬ (NP).active history.state who := by
      cases current : history.state with
      | none => rw [current] at ended; exact ended.elim
      | some control =>
        change control.actor ≠ some who
        rw [current] at ended
        change control.remaining = 0 ∧ control.actor = none at ended
        simp [ended.2]
    rw [← (N).behavioral_eq_of_not_active
      (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
        positive le_one
        weights n who) (sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy
          who)
        history.trace
          inactive]
    exact lower

include wellFormed covers capacity opportunity inclusion timely completes assembled in
/-- Actual native projection of common recovery play has only the retained
honest mass available for a public failure, including at initialization. -/
theorem sourceNativeProfile_initialized_failure_mass_le_of_counted_service :
    (((N).runBehavioral (sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy)
      (2 * horizon + 1)).toOuterMeasure {history | ¬ Clear history.state}).toReal ≤
      (min (Fintype.card Player) 1 * horizon : ℕ) * (1 - slotRetention (scale n)) := by
  classical
  let certificate := ((NMenu).bounded (initialLaw setup) horizon
    (RecoveryProjection.nativeScheduler runtime leaks scheduler)).wellFoundedHistories
  let honest := honestProfile setup runtime leaks bounds (initialLaw setup) horizon
    (RecoveryProjection.nativeScheduler runtime leaks scheduler)
    (sequence n)
  have dominates := sourceNativeProfile_dominatesHonestFrom_initialized_of_counted_service
    (runtime := runtime)
    setup leaks bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights n fallback strategy
      assembled opportunity inclusion timely completes certificate
  have close := onePacket_bounded_withinTV_honest setup runtime leaks bounds (initialLaw setup)
    horizon
    (RecoveryProjection.nativeScheduler runtime leaks scheduler) (sequence n) _
      (slotRetention_nonneg (positive n).le (le_one n))
    (slotRetention_le_one (positive n).le (le_one n)) dominates
  have honestClear : (((N).runBehavioral honest (2 * horizon + 1)).toOuterMeasure
      {history | ¬ Clear history.state}).toReal = 0 := by
    rw [← expect_indicator]
    trans expect ((N).runBehavioral honest (2 * horizon + 1)) (fun _ => (0 : ℝ))
    · apply expect_congr_on_support
      intro history member
      have clear : Clear history.state := by
        cases current : history.state with
        | none => trivial
        | some control =>
          obtain ⟨point, decoded, intended⟩ := counted_honest_initialized_intended (runtime :=
            runtime)
            opportunity inclusion timely
            completes wellFormed covers capacity (sequence n) certificate (2 * horizon + 1)
              history member control current
          exact exclusionEvidence_of_decodedIntended (runtime := runtime)
            ((NMenu).toRawTrace (initialLaw setup) horizon
              (RecoveryProjection.nativeScheduler runtime leaks scheduler)
              (current ▸ history.trace)) decoded intended
      simp [clear]
    · exact expect_zero _
  have bound := close.symm {history | ¬ Clear history.state}
  rw [honestClear, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at bound
  exact bound

end Vegas.RecoveryOnePacket
