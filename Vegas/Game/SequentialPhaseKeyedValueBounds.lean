/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryKeyedValueBounds
import Vegas.Game.SequentialPhasePendingValueAffine
import Vegas.Game.SequentialPhaseNativeComparison

/-! # Common keyed scores under actual phase component weights -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

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

local notation "Menu" => bounds.onePacketMenu (runtime setup) (RecoveryLeaks)

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) (RecoveryLeaks)) (Vegas.initialLaw setup) horizon
    (nativeScheduler)

local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

variable {Public : Type*} {signal : State L setup.context → Public}

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

include opportunity inclusion timely completes in
open Classical in
/-- The constructed native comparison has shared keyed failure scores and a
uniformly vanishing affine value error under the original phase service assumptions. -/
theorem nativeComparison_keyed_value_bounds [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup (RecoveryLeaks) bounds horizon (nativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ (failureScore : ℕ → LateKey setup (RecoveryLeaks) → LateOption bounds.candidateCount → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ failureScore n key option ∧ failureScore n key option ≤ 1) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup (RecoveryLeaks) bounds horizon (nativeScheduler) ((N).agentAt site)
            →
        ¬ Vegas.OwingAgent setup (RecoveryLeaks) bounds horizon (nativeScheduler) ((N).agentAt site)
            →
        ownedKeyed (Vegas.FreeAgent setup (RecoveryLeaks) bounds horizon (nativeScheduler))
          (LateDeliveryAgent setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
            (nativeScheduler))
          ((N).agentAt site) →
        ∀ key, lateKey setup (RecoveryLeaks) who site.1 = some key → ∀ option,
        let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
          positive le_one weights n
        let certificate := ((Menu).bounded (Vegas.initialLaw setup) horizon
          (nativeScheduler)).wellFoundedHistories
        let law := onePacketLate setup (RecoveryLeaks) bounds horizon (nativeScheduler) sequence
            scale
          positive
          le_one n ((N).agentAt site) option
        let installed := Profile.update (sig := (N).behavioralSignature) target.strategy who
          ((target.strategy who).withLaw site.1 law)
        let stopped := fun final : (NP).History => ¬ Clear final.state ∨
          DecodedState setup (RecoveryLeaks) (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        |expect (target.belief who site) (fun history =>
            expect ((N).runBehavioralUntil certificate installed stopped history.1)
              (fun final => if stopped final then excludedPayoff who else
                exclusionBase setup parameter utility excludedPayoff (RecoveryLeaks) final.state
                    who)) -
          (excludedPayoff who + (1 - failureScore n key option) *
            (siteValue setup (RecoveryLeaks) bounds horizon (nativeScheduler) parameter utility
              excludedPayoff target (setup.intendedOpeningProfile (sequence n).strategy) site -
                excludedPayoff who))| ≤
          error n := by
  apply RecoveryOnePacket.nativeComparison_keyed_value_bounds_of_pending setup (RecoveryLeaks)
      bounds
    horizon (recoveryScheduler setup leaks scheduler) wellFormed independent observable sequence
    sourceMixed scale positive le_one scaleEq covers coversInputs capacity slots_pos
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) parameter
    utility excludedPayoff payoffBound boundNonneg readoutBounded excludedBounded 1 (by norm_num)
  intro n who site late debtFree key siteKey event pending past view atSite option
    target common certificate law installed stopped payoff error history forced
  refine (nativeComparison_pending_value_affine setup leaks bounds horizon scheduler opportunity
    inclusion timely completes wellFormed covers capacity sequence scale positive le_one weights n
    site (Or.inl late) debtFree siteKey pending atSite law history forced (Or.inl ⟨option, rfl⟩)
    parameter utility excludedPayoff boundNonneg (readoutBounded who)
    (excludedBounded who)).trans ?_
  dsimp only [error]
  simp only [one_mul, le_refl]

end Vegas.SequentialPhase
