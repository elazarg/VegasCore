/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNonLateSourceValue
import Vegas.Game.RecoveryCompletionPotential

/-! # Continuation transport through a local source-event response -/

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
/-- The common future value is approximated by the physical completion value,
with exceptional mass expressed by the current-event bad-stop observable. -/
theorem nativeComparison_local_completion_value_sub_le_of_boundary_values [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    (terminalCompletes : ∀ (final : (application setup leaks).Control),
      ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
        (NativeScheduler)).Trace (some final) →
      ExclusionEvidence 0 ∅ (⟨final.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      (application setup leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
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
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    (boundaryValues : ∀ (nextRank : Nat) (start : (NP).History)
      (anchor : (application setup leaks).Execution),
      start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ →
      ReachedBoundary setup leaks horizon (NativeScheduler) nextRank anchor →
      ∀ point : ProtocolState setup.program,
      sourceServicePrefix? setup nextRank anchor.application.config = some point →
      ProtocolState.Intended setup.program point →
      let stopped := fun final : (NP).History => ¬ Clear final.state ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state
      |expect ((N).runBehavioralUntil certificate
          (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive
            le_one weights n) stopped start)
          (fun final => if stopped final then excludedPayoff who else
            exclusionBase setup parameter utility excludedPayoff leaks final.state who) -
        sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who point| ≤
        (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
          (application setup leaks).rank horizon start.state) :
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
  intro common installed phase stopped fresh phaseLaw
  have clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅) :=
    exclusionEvidence_of_decodedIntended
      ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
        (NativeScheduler) (current ▸ history.trace))
      ((decodedPoint_eq_of_isPrefix ordered).trans decoded) intended
  have evaluated := pending_completionValue_eq_potential terminalCompletes certificate installed
    history current ordered clear event
    ready (setup.intendedOpeningProfile (sequence n).strategy) parameter utility excludedPayoff who
    fresh (fun _ => excludedPayoff who)
  have badMass := pending_badMass_eq_lateBadStop terminalCompletes certificate installed history
    current ordered clear event
    ready key decided fresh
  have comparison := nativeComparison_local_phase_value_sub_le_of_boundary_values setup leaks
    bounds horizon scheduler sequence scale positive le_one weights n terminalCompletes certificate
    who info law history current observed event ready owned key decided ordered point decoded
    intended parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
    boundaryValues
  rw [evaluated]
  dsimp only at comparison
  rw [badMass] at comparison
  exact comparison


open Classical in
/-- The common future value is approximated by the physical completion value,
with exceptional mass expressed by the current-event bad-stop observable. -/
theorem nativeComparison_local_completion_value_sub_le [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
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
    (Recovery.CompletesPlay.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) completes)
    certificate who info law history current observed event ready owned key decided ordered point
    decoded intended parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
  intro nextRank start anchor state boundary target atRank targetIntended
  exact nativeComparison_stopped_boundary_value_sub_le setup leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion timely
    completes certificate nextRank start anchor state boundary target atRank targetIntended
    parameter utility excludedPayoff who boundNonneg readoutBounded excludedBounded

end Vegas.RecoveryOnePacket
