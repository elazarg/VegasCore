/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryInitializedCounted
import Vegas.Game.SequentialPhaseHonestLaw
import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.OnePacketHonestTerminalApproximation

/-! # Initialized native projections of actual phase comparison mixtures -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : PhaseService.Opportunity runtime leaks (phaseInitialLaw setup) horizon
    scheduler delay)
  (inclusion : PhaseService.ProtectedInclusion runtime leaks (phaseInitialLaw setup) horizon
    scheduler bound)
  (timely : runtime.AsyncTimely delay bound)
  (completes : PhaseService.CompletesPlay runtime leaks (phaseInitialLaw setup) horizon
    scheduler)

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (recoveryScheduler setup runtime leaks scheduler)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (nativeScheduler)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)
local notation "NativeModel" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup)
  horizon (nativeScheduler)
local notation "NativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

include opportunity inclusion timely completes in
theorem component_projection_dominates_honest_initialized
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p)) (n : ℕ)
    (certificate : (NP).WellFoundedHistories) :
    DominatesHonestFrom (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
      horizon
        (nativeScheduler)
      (sequence n) (slotRetention (scale n))
      (RecoveryOnePacket.sourceNativeProfile (runtime := runtime) setup (RecoveryLeaks) bounds
        horizon
          (RecoveryScheduler)
      (recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler (sequence n) (scale
        n)
        (positive n).le (le_one n) (weights n))) (NP).initHistory := by
  exact
    RecoveryOnePacket.sourceNativeProfile_dominatesHonestFrom_initialized_of_counted_service
      (runtime := runtime)
      setup (RecoveryLeaks) bounds horizon (RecoveryScheduler)
    wellFormed covers capacity sequence scale positive le_one
    (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights n)) n
    (recoveryComparisonFallback setup runtime leaks bounds horizon scheduler)
    (recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler (sequence n) (scale n)
      (positive n).le (le_one n) (weights n)) rfl
    (fun control trace clear => PhaseService.Opportunity.clear_native_counted setup runtime leaks
      bounds
      horizon scheduler delay opportunity trace clear)
    (fun control trace clear => PhaseService.ProtectedInclusion.clear_native_counted setup runtime
      leaks
      bounds horizon scheduler bound inclusion trace clear)
    timely
    (fun control trace clear terminal => PhaseService.CompletesPlay.clear_native_counted setup
      runtime
      leaks bounds horizon scheduler completes trace clear terminal)
    certificate

include opportunity inclusion timely completes in
theorem component_projection_initialized_failure_mass_le
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p)) (n : ℕ)
 :
    (((N).runBehavioral (RecoveryOnePacket.sourceNativeProfile (runtime := runtime) setup
      (RecoveryLeaks) bounds
      horizon (RecoveryScheduler)
      (recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler (sequence n) (scale
        n)
        (positive n).le (le_one n) (weights n))) (2 * horizon + 1)).toOuterMeasure
      {history | ¬ ReactiveApplication.stateInvariant (app := application (runtime := runtime)
        setup (RecoveryLeaks))
        (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅)) history.state}).toReal ≤
      (min (Fintype.card Player) 1 * horizon : ℕ) * (1 - slotRetention (scale n)) := by
  exact RecoveryOnePacket.sourceNativeProfile_initialized_failure_mass_le_of_counted_service
    (runtime := runtime)
    setup (RecoveryLeaks) bounds horizon (RecoveryScheduler)
    wellFormed covers capacity sequence scale positive le_one
    (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights n)) n
    (recoveryComparisonFallback setup runtime leaks bounds horizon scheduler)
    (recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler (sequence n) (scale n)
      (positive n).le (le_one n) (weights n)) rfl
    (fun control trace clear => PhaseService.Opportunity.clear_native_counted setup runtime leaks
      bounds
      horizon scheduler delay opportunity trace clear)
    (fun control trace clear => PhaseService.ProtectedInclusion.clear_native_counted setup runtime
      leaks
      bounds horizon scheduler bound inclusion trace clear)
    timely
    (fun control trace clear terminal => PhaseService.CompletesPlay.clear_native_counted setup
      runtime
      leaks bounds horizon scheduler completes trace clear terminal)

include opportunity inclusion timely completes in
theorem component_projection_initialized_readout_withinTV
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p)) (n : ℕ)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    PMF.WithinTV ((min (Fintype.card Player) 1 * horizon : ℕ) *
      (1 - slotRetention (scale n)))
      (((N).runBehavioral (RecoveryOnePacket.sourceNativeProfile (runtime := runtime) setup
        (RecoveryLeaks) bounds
        horizon (RecoveryScheduler)
      (recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler (sequence n) (scale
        n)
        (positive n).le (le_one n) (weights n))) (2 * horizon + 1)).map
        (readoutExclusion (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw
          setup) horizon
          (nativeScheduler) parameter utility excludedPayoff))
      ((setup.intendedModel.runBehavioral (sequence n).strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff)) := by
  classical
  let certificate := ((bounds.onePacketMenu runtime (RecoveryLeaks)).bounded
    (Vegas.initialLaw setup) horizon (nativeScheduler)).wellFoundedHistories
  have honestLaw := honest_initialized_readout_law setup runtime leaks bounds horizon scheduler
    opportunity inclusion timely completes wellFormed covers capacity (sequence n) certificate
  rw [(N).runBehavioralTerminalFrom_initHistory certificate
    (honestProfile (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
      horizon (nativeScheduler)
      (sequence n))
    ((bounds.onePacketMenu runtime (RecoveryLeaks)).bounded (Vegas.initialLaw setup) horizon
      (nativeScheduler))] at honestLaw
  exact onePacket_bounded_readout_exclusion_withinTV (runtime := runtime) setup (RecoveryLeaks)
    bounds
    (Vegas.initialLaw setup)
    horizon (nativeScheduler) parameter utility excludedPayoff (sequence n) (sequence n).strategy
    (instructionCount setup.program + 1) honestLaw
    (slotRetention_nonneg (positive n).le (le_one n))
    (slotRetention_le_one (positive n).le (le_one n)) _
    (component_projection_dominates_honest_initialized setup runtime leaks bounds horizon scheduler
      opportunity inclusion timely completes wellFormed covers capacity sequence scale positive
      le_one weights n certificate)

end Vegas.SequentialPhase
