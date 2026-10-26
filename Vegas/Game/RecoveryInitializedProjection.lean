/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryInitializedCoupling
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryInitializedCounted
import Vegas.Game.RecoveryInitializedLaw
import Vegas.Game.RecoveryNativePrior
import Vegas.Game.RecoveryExclusionPayoff
import Vegas.Pending.ExclusionTerminalClearance
import Vegas.Game.OnePacketHonestTerminalApproximation

/-! # Initialized laws of the actual common recovery strategy -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "RawN" => ReactiveApplication.information (application setup leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)
local notation "RawR" => ReactiveApplication.information
  (recoveryApplication (runtime setup) leaks) Initial horizon scheduler
local notation "RawNP" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)
local notation "RawRP" => ReactiveApplication.protocol
  (recoveryApplication (runtime setup) leaks) Initial horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

variable [Fintype ((ReactiveApplication.ResponseMenu.protocol (Recovery.onePacketMenu (runtime
    setup) leaks bounds) (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState
    (graph setup))) (initialLaw setup)) horizon scheduler)).History]
  [(application setup leaks).FiniteNature (initialLaw setup) ((nativeScheduler (runtime setup)
    leaks scheduler))]
  [∀ who, DecidableEq (((model setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler)).InfoState
    who)]
  (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
  (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
  (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
  (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
  {slots : Nat}
  (weights : ℕ → ∀ p, PMF (Part setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler slots p)) (n : ℕ)
  (fallback : ∀ who, ((model setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler)).Policy
    who) (strategy : ∀ who, ((model setup leaks bounds (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).BehavioralPolicy who)
  (assembled : strategy = ((model setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).agentBehavior ((model setup leaks bounds (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)).playedInformation fallback
    (fun agent => (weights n (pool setup leaks bounds (PMF.map (fun native => (RecoveryState.mk
    native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler agent)).bind
      (component setup leaks bounds (PMF.map (fun native => (RecoveryState.mk native ∅ :
    RecoveryState (graph setup))) (initialLaw setup)) horizon scheduler (sequence n) (scale n)
        (positive n).le (le_one n) agent)))
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks (PMF.map (fun native =>
    (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)) horizon
    scheduler)
include wellFormed covers capacity opportunity inclusion timely completes assembled in
/-- Actual common recovery strategies retain initialized honest native play;
only the original completion weights are used. -/
theorem sourceNativeProfile_dominatesHonestFrom_initialized
    (certificate : (NP).WellFoundedHistories) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
      (sequence n) (slotRetention (scale n))
      (sourceNativeProfile setup leaks bounds horizon scheduler strategy) (NP).initHistory := by
  exact sourceNativeProfile_dominatesHonestFrom_initialized_of_counted_service setup leaks
    bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n fallback strategy assembled
    (Recovery.Opportunity.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) opportunity)
    (Recovery.ProtectedInclusion.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) inclusion) timely
    (Recovery.CompletesPlay.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) completes)
    certificate

include wellFormed covers capacity opportunity inclusion timely completes assembled in
/-- Actual native projection of common recovery play has only the retained
honest mass available for a public failure, including at initialization. -/
theorem sourceNativeProfile_initialized_failure_mass_le :
    (((N).runBehavioral (sourceNativeProfile setup leaks bounds horizon scheduler strategy)
      (2 * horizon + 1)).toOuterMeasure {history | ¬ Clear history.state}).toReal ≤
      (min (Fintype.card Player) 1 * horizon : ℕ) * (1 - slotRetention (scale n)) := by
  exact sourceNativeProfile_initialized_failure_mass_le_of_counted_service setup leaks bounds
    horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n fallback strategy assembled
    (Recovery.Opportunity.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) opportunity)
    (Recovery.ProtectedInclusion.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) inclusion) timely
    (Recovery.CompletesPlay.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) completes)

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

include wellFormed covers capacity opportunity inclusion timely completes assembled in
/-- The initialized joint typed-readout and realized base-payoff law of the
actual common recovery strategy approaches its original intended source law. -/
theorem recovery_initialized_readout_withinTV :
    PMF.WithinTV (2 * ((min (Fintype.card Player) 1 * horizon : ℕ) *
      (1 - slotRetention (scale n))))
      (((R).runBehavioral strategy (2 * horizon + 1)).map (fun final =>
        (sourceReadout setup leaks (protocolState (runtime setup) leaks final.state),
          recoveryExclusionBase parameter utility excludedPayoff final.state)))
      ((setup.intendedModel.runBehavioral (sequence n).strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff)) := by
  classical
  let certificate := ((NMenu).bounded (initialLaw setup) horizon
    (NativeScheduler)).wellFoundedHistories
  have close := recovery_initialized_projection_withinTV setup leaks bounds horizon scheduler
    strategy
    (fun state => (sourceReadout setup leaks state,
      exclusionBase setup parameter utility excludedPayoff leaks state))
    (fun state => (sourceReadout setup leaks (protocolState (runtime setup) leaks state),
      recoveryExclusionBase parameter utility excludedPayoff state)) (by
        intro state clear
        refine Prod.ext rfl ?_
        funext who
        cases state with
        | none => rfl
        | some control =>
          exact recoveryExclusionBase_of_not_excluded parameter utility excludedPayoff control who
            (by simp [clear control rfl]))
  have boundedClose := close.mono (sourceNativeProfile_initialized_failure_mass_le setup leaks
    bounds horizon scheduler wellFormed covers capacity sequence scale positive le_one weights n
      fallback strategy assembled opportunity inclusion timely completes)
  have honestLaw := recovery_honest_initialized_readout_law (initialLaw_initialized setup)
    (initialLaw_native setup) opportunity inclusion timely completes wellFormed covers capacity
      (sequence n) certificate
  rw [(N).runBehavioralTerminalFrom_initHistory certificate
    (honestProfile setup leaks bounds (initialLaw setup) horizon (NativeScheduler) (sequence n))
      ((NMenu).bounded (initialLaw setup) horizon (NativeScheduler))] at honestLaw
  have nativeClose := onePacket_bounded_readout_exclusion_withinTV setup leaks bounds
    (initialLaw setup)
    horizon (NativeScheduler) parameter utility excludedPayoff (sequence n) (sequence n).strategy
    (instructionCount setup.program + 1) honestLaw
      (slotRetention_nonneg (positive n).le (le_one n))
      (slotRetention_le_one (positive n).le (le_one n))
      (sourceNativeProfile setup leaks bounds horizon scheduler strategy)
      (sourceNativeProfile_dominatesHonestFrom_initialized setup leaks bounds horizon scheduler
        wellFormed covers capacity sequence scale positive le_one weights n fallback strategy
          assembled opportunity inclusion timely completes certificate)
  simpa only [two_mul] using boundedClose.trans nativeClose

include wellFormed covers capacity opportunity inclusion timely completes in
/-- A common completion sequence has a uniform vanishing initialized joint-law
error against the same original source assessment sequence. -/
theorem recovery_initialized_lawApproximation
    (strategies : ℕ → ∀ who, (R).BehavioralPolicy who)
    (allAssembled : ∀ n, strategies n = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (vanishing : Filter.Tendsto scale Filter.atTop (nhds 0)) :
    ∃ lawError : ℕ → ℝ, Filter.Tendsto lawError Filter.atTop (nhds 0) ∧
      ∀ n outcome,
        |((((R).runBehavioral (strategies n) (2 * horizon + 1)).map (fun final =>
            (sourceReadout setup leaks (protocolState (runtime setup) leaks final.state),
              recoveryExclusionBase parameter utility excludedPayoff final.state)))
                outcome).toReal -
          (((setup.intendedModel.runBehavioral (sequence n).strategy
            (instructionCount setup.program + 1)).map
            (intendedReadoutExclusion setup parameter utility excludedPayoff)) outcome).toReal| ≤
          lawError n := by
  refine ⟨fun n => 2 * ((min (Fintype.card Player) 1 * horizon : ℕ) *
    (1 - slotRetention (scale n))), ?_, fun n outcome => ?_⟩
  · have retained := tendsto_slotRetention vanishing
    have difference := (tendsto_const_nhds (x := (1 : ℝ))).sub retained
    have converges := (difference.const_mul
      ((min (Fintype.card Player) 1 * horizon : ℕ) : ℝ)).const_mul 2
    simpa using converges
  · exact (recovery_initialized_readout_withinTV setup leaks bounds horizon scheduler wellFormed
      covers capacity sequence scale positive le_one weights n fallback (strategies n)
      (allAssembled n) opportunity inclusion timely completes parameter utility
        excludedPayoff).apply
        outcome

end Vegas.RecoveryOnePacket
