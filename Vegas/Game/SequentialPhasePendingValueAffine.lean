/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPendingValueAffine
import Vegas.Game.SequentialPhaseNativeContinuationValue
import Vegas.Game.SequentialPhaseNativeComparison

/-! # Pending affine values from physical singleton phase service -/

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

local notation "Menu" => bounds.onePacketMenu runtime (RecoveryLeaks)

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application (runtime := runtime) setup (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

include opportunity inclusion timely completes in
open Classical in
/-- The actual phase comparison has the native pending affine value estimate,
including binding and disclosure choices, under physical phase service alone. -/
theorem nativeComparison_pending_value_affine
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds horizon scheduler bounds.candidateCount p)) (n : ℕ)
    {who : Player} (site : (N).InformationSite who)
    (pendingSite : LateDelivery (runtime := runtime) setup (RecoveryLeaks) who site.1 ∨
      FirstActivation (runtime := runtime) setup (RecoveryLeaks) who site.1)
    (debtFree : SiteDebtFree (runtime := runtime) setup (RecoveryLeaks) bounds horizon
      (nativeScheduler) site)
    {key : LateKey (runtime := runtime) setup (RecoveryLeaks)} (siteKey : lateKey (runtime :=
      runtime) setup (RecoveryLeaks) who site.1 = some
        key)
    {event : (graph setup).EventId}
    (pending : pendingEvent (runtime := runtime) setup (RecoveryLeaks) who site.1 = some event)
    {past : List (application (runtime := runtime) setup (RecoveryLeaks)).PlayerEntry}
    {view : (application (runtime := runtime) setup (RecoveryLeaks)).PlayerView} (atSite : site.1
      = some (past, view))
    (law : PMF ((N).Choice who site.1))
    (history : (N).InformationHistory who site.1)
    (forced : ForcedState (runtime := runtime) setup (RecoveryLeaks) who history.1.state)
    (lawShape : (∃ option : LateOption bounds.candidateCount,
      law = onePacketLate (runtime := runtime) setup (RecoveryLeaks) bounds horizon
        (nativeScheduler) sequence scale
          positive
        le_one n ((N).agentAt site) option) ∨
      law = PMF.pure (silenceChoice (runtime := runtime) setup (RecoveryLeaks) bounds
        (Vegas.initialLaw setup) horizon
        (nativeScheduler) who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let common := (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence
      scale
      positive le_one weights n).strategy
    let certificate := ((Menu).bounded (Vegas.initialLaw setup) horizon
      (nativeScheduler)).wellFoundedHistories
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState (runtime := runtime) setup (RecoveryLeaks) (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase (runtime := runtime) setup parameter utility excludedPayoff (RecoveryLeaks)
        final.state who
    let failure := expect ((N).runBehavioralFrom installed (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
    |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      ((1 - failure) *
        decodedPointValue (runtime := runtime) setup (RecoveryLeaks) bounds horizon
          (nativeScheduler) parameter utility
          excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
          (siteRank (runtime := runtime) site.1) history.1 +
        failure * excludedPayoff who)| ≤
      (2 * payoffBound * (1 - slotRetention (scale n))) *
        (2 * horizon + 1) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) := by
  intro common certificate installed stopped payoff failure
  apply RecoveryOnePacket.nativeComparison_pending_value_affine_of_boundary_values (runtime :=
    runtime) setup
      (RecoveryLeaks)
    bounds horizon (recoveryScheduler setup runtime leaks scheduler) wellFormed covers capacity
      sequence
    scale
    positive le_one
    (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights n)) n
    (fun control trace clear ended => PhaseService.CompletesPlay.clear_native_counted setup
      runtime leaks
      bounds horizon scheduler completes trace clear ended)
    site pendingSite debtFree siteKey pending atSite law history forced lawShape parameter utility
    excludedPayoff boundNonneg readoutBounded excludedBounded
    (2 * payoffBound * (1 - slotRetention (scale n))) (by
      have retention := slotRetention_le_one (positive n).le (le_one n)
      positivity)
  intro nextRank start anchor state boundary target atRank targetIntended
  exact nativeComparison_stopped_boundary_value_sub_le setup runtime leaks bounds horizon scheduler
    opportunity inclusion timely completes wellFormed covers capacity sequence scale positive le_one
    weights n certificate nextRank start anchor state boundary target atRank targetIntended
    parameter utility excludedPayoff who boundNonneg readoutBounded excludedBounded

end Vegas.SequentialPhase
