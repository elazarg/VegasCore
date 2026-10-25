/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryLocalCompletionValue
import Vegas.Game.SequentialPhaseNativeContinuationValue
import Vegas.Game.SequentialPhaseNativeComparison

/-! # Local completion values from physical singleton phase service -/

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

local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

include opportunity inclusion timely completes in
open Classical in
/-- The actual phase comparison weights factor the current event's value through
its physical source completion with the original honest-tail error bound. -/
theorem nativeComparison_local_completion_value_sub_le
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ)
    (certificate : (NP).WellFoundedHistories) (who : Player) (info : (N).InfoState who)
    (law : PMF ((N).Choice who info)) (history : (NP).History)
    {remaining : Nat} {execution : (application setup (RecoveryLeaks)).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (observed : (N).infoOf who history.trace = info)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who) (key : LateKey setup (RecoveryLeaks))
    (decided : decidedEvent key = some event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let common := (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n).strategy
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw info law)
    let phase := fun final : (NP).History =>
      LateStopped setup (RecoveryLeaks) bounds horizon (nativeScheduler) rank final ∨ ¬ Clear
          final.state
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup (RecoveryLeaks) (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let fresh := fun control : (application setup (RecoveryLeaks)).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event
    let phaseLaw := (N).runBehavioralUntil certificate installed phase history
    |expect ((N).runBehavioralUntil certificate installed stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff (RecoveryLeaks) final.state who) -
      expect phaseLaw (completionValue setup (RecoveryLeaks) bounds horizon (nativeScheduler)
          parameter
        utility excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) rank fresh who
        (fun _ => excludedPayoff who))| ≤
      (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1) +
      2 * payoffBound * expect phaseLaw
        (lateBadStop setup (RecoveryLeaks) bounds horizon (nativeScheduler) rank fresh event) := by
  apply RecoveryOnePacket.nativeComparison_local_completion_value_sub_le_of_boundary_values setup
    (RecoveryLeaks) bounds horizon (recoveryScheduler setup leaks scheduler) sequence scale positive
    le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n
    (fun control trace clear ended => PhaseService.CompletesPlay.clear_native_counted setup leaks
      bounds horizon scheduler completes trace clear ended)
    certificate who info law history current observed event ready owned key decided ordered point
    decoded intended parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
  intro nextRank start anchor state boundary target atRank targetIntended
  exact nativeComparison_stopped_boundary_value_sub_le setup leaks bounds horizon scheduler
    opportunity inclusion timely completes wellFormed covers capacity sequence scale positive le_one
    weights n certificate nextRank start anchor state boundary target atRank targetIntended
    parameter
    utility excludedPayoff who boundNonneg readoutBounded excludedBounded

end Vegas.SequentialPhase
