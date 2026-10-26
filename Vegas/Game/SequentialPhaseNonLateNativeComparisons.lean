/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNonLateNativeComparisons
import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.SequentialPhaseNativeComparison

/-! # Source incentive bounds for nonlate native phase responses -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

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

variable {Public : Type*} {signal : State L setup.context → Public}

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

include opportunity inclusion timely completes in
open Classical in
/-- Every pure native nonlate pending response under physical phase service
is bounded by exclusion or an original source deviation, with a uniform vanishing error. -/
theorem nativeComparison_nonlate_pending_comparisons [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor (runtime := runtime) setup (RecoveryLeaks) bounds horizon (nativeScheduler)
        (sequence n))
      (2 * horizon + 2) n)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds horizon scheduler bounds.candidateCount p))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who) (choice : (N).Choice who site.1),
        ¬ Vegas.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon
          (nativeScheduler) ((N).agentAt site)
            →
        ¬ Vegas.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon
          (nativeScheduler) ((N).agentAt site)
            →
        ¬ LateDelivery (runtime := runtime) setup (RecoveryLeaks) who site.1 →
        ∀ {event : (graph setup).EventId}, pendingEvent (runtime := runtime) setup (RecoveryLeaks)
          who site.1 = some
            event →
        let common := (nativeComparisonSequence setup runtime leaks bounds horizon scheduler
          sequence scale
          positive le_one weights n).strategy
        let certificate := ((Menu).bounded (Vegas.initialLaw setup) horizon
          (nativeScheduler)).wellFoundedHistories
        let stopped := fun final : (NP).History => ¬ Clear final.state ∨
          DecodedState (runtime := runtime) setup (RecoveryLeaks) (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
          exclusionBase (runtime := runtime) setup parameter utility excludedPayoff
            (RecoveryLeaks) final.state who
        let gain := expect ((nativeComparisonSequence setup runtime leaks bounds horizon scheduler
          sequence
          scale positive le_one weights n).belief who site) (fun history =>
            expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
              expect ((N).runBehavioralUntil certificate common stopped history.1) payoff)
        gain ≤ error n ∨ ∃ sourceDeviation : setup.intendedModel.AssessmentDeviation who,
          gain ≤ intendedSiteGain setup parameter utility excludedPayoff (sequence n)
            sourceDeviation + error n := by
  exact RecoveryOnePacket.nativeComparison_nonlate_pending_comparisons_of_counted_service (runtime
    := runtime) setup
    (RecoveryLeaks) bounds horizon (recoveryScheduler setup runtime leaks scheduler) wellFormed
      independent
    observable covers coversInputs capacity sequence sourceMixed sourceBayes scale positive le_one
    scaleEq (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler
      (weights n))
    (fun _ trace clear => PhaseService.Opportunity.clear_native_counted setup runtime leaks bounds
      horizon
      scheduler delay opportunity trace clear)
    (fun _ trace clear => PhaseService.ProtectedInclusion.clear_native_counted setup runtime leaks
      bounds
      horizon scheduler bound inclusion trace clear) timely
    (fun _ trace clear ended => PhaseService.CompletesPlay.clear_native_counted setup runtime
      leaks bounds
      horizon scheduler completes trace clear ended)
    parameter utility excludedPayoff below upper le_upper boundNonneg readoutBounded excludedBounded

end Vegas.SequentialPhase
