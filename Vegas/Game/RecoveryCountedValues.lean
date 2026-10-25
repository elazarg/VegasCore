/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComparisonContinuationValue
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryLocalCompletionValue
import Vegas.Game.RecoveryNonLateSourceValue
import Vegas.Game.RecoveryComparisonRetention
import Vegas.Game.RecoveryStoppedContinuationValue
import Vegas.Game.RecoveryComparisonContinuationValue

/-! # Native comparison values under counted service -/

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
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

open Classical in
theorem nativeComparison_local_completion_value_sub_le_of_counted_service [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      OpportunityAt (runtime setup) leaks control.execution delay)
    (inclusion : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      ProtectedInclusionAt (runtime setup) leaks control.execution bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (NP).WellFoundedHistories) (who : Player) (info : (N).InfoState who)
    (law : PMF ((N).Choice who info)) (history : (NP).History)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (observed : (N).infoOf who history.trace = info)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who) (key : LateKey setup leaks)
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
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw info law)
    let phase := fun final : (NP).History =>
      LateStopped setup leaks bounds horizon (NativeScheduler) rank final ∨ ¬ Clear final.state
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let fresh := fun control : (application setup leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event
    let phaseLaw := (N).runBehavioralUntil certificate installed phase history
    |expect ((N).runBehavioralUntil certificate installed stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who) -
      expect phaseLaw (completionValue setup leaks bounds horizon (NativeScheduler) parameter
        utility excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) rank fresh who
        (fun _ => excludedPayoff who))| ≤
      (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1) +
      2 * payoffBound * expect phaseLaw
        (lateBadStop setup leaks bounds horizon (NativeScheduler) rank fresh event) := by
  apply nativeComparison_local_completion_value_sub_le_of_boundary_values setup leaks bounds horizon
    scheduler sequence scale positive le_one weights n
    completes
    certificate who info law history current observed event ready owned key decided ordered point
    decoded intended parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
  intro nextRank start anchor state boundary target atRank targetIntended
  exact nativeComparison_stopped_boundary_value_sub_le_of_counted_service setup leaks bounds
    horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion timely
    completes certificate nextRank start anchor state boundary target atRank targetIntended
    parameter utility excludedPayoff who boundNonneg readoutBounded excludedBounded

open Classical in
theorem nativeComparison_local_phase_value_sub_le_of_counted_service [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      OpportunityAt (runtime setup) leaks control.execution delay)
    (inclusion : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      ProtectedInclusionAt (runtime setup) leaks control.execution bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (NP).WellFoundedHistories) (who : Player) (info : (N).InfoState who)
    (law : PMF ((N).Choice who info)) (history : (NP).History)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (observed : (N).infoOf who history.trace = info)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who) (key : LateKey setup leaks)
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
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw info law)
    let phase := fun final : (NP).History =>
      LateStopped setup leaks bounds horizon (NativeScheduler) rank final ∨ ¬ Clear final.state
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let fresh := fun control : (application setup leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event
    let phaseLaw := (N).runBehavioralUntil certificate installed phase history
    let potential := fun final =>
      (completionPoint setup leaks bounds horizon (NativeScheduler) rank fresh final).elim
        (excludedPayoff who) (sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who)
    |expect ((N).runBehavioralUntil certificate installed stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who) -
      expect phaseLaw potential| ≤
      (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1) +
      2 * payoffBound * (phaseLaw.toOuterMeasure
        {final | completionPoint setup leaks bounds horizon (NativeScheduler) rank fresh final =
          none ∧ ¬ DecisionFailed key final.state}).toReal := by
  apply nativeComparison_local_phase_value_sub_le_of_boundary_values setup leaks bounds horizon
    scheduler sequence scale positive le_one weights n
    completes
    certificate who info law history current observed event ready owned key decided ordered point
    decoded intended parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
  intro nextRank start anchor state boundary target atRank targetIntended
  exact nativeComparison_stopped_boundary_value_sub_le_of_counted_service setup leaks bounds
    horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion timely
    completes certificate nextRank start anchor state boundary target atRank targetIntended
    parameter utility excludedPayoff who boundNonneg readoutBounded excludedBounded

end Vegas.RecoveryOnePacket
