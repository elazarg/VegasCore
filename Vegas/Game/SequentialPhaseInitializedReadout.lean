/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonRetention
import Vegas.Game.SequentialPhaseHonestLaw
import Vegas.Game.OnePacketLawApproximation
import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.OnePacketHonestTerminalApproximation

/-! # Initialized native comparison readouts under physical phase service -/

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

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

include opportunity inclusion timely completes in
/-- The actual native comparison's joint typed terminal readout and realized
base payoff law approaches the intended source law under physical phase service. -/
theorem nativeComparison_initialized_readout_withinTV
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
      (((N).runBehavioral
        (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
          positive
          le_one weights n).strategy (2 * horizon + 1)).map
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
    (nativeComparison_dominatesHonestFrom_initialized setup runtime leaks bounds horizon scheduler
      opportunity inclusion timely completes wellFormed covers capacity sequence scale positive
      le_one weights n certificate)

end Vegas.SequentialPhase
