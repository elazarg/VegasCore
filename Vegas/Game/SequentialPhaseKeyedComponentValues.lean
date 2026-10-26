/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeValueError
import Vegas.Game.SequentialPhaseKeyedValueBounds
import Vegas.Game.SequentialPhaseKeyedLaw

/-! # Affine keyed component values in the original phase game -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu runtime (RecoveryLeaks)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) RecoveryPrior horizon
  (RecoveryScheduler)
local notation "NP" => onePacketProtocol (runtime := runtime) setup (RecoveryLeaks) bounds horizon
  (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application (runtime := runtime) setup
  (RecoveryLeaks))
  (PMF.map RecoveryState.native (RecoveryPrior)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application (runtime :=
  runtime) setup
    (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local notation "P" => phaseApplication runtime leaks
local notation "M" => model setup runtime leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information runtime leaks
    (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

variable {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- The actual phase component values have common affine keyed scores, with a
uniformly vanishing error and only the intended terminal punishment floor. -/
theorem keyed_component_value_bounds [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler)
        (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity runtime leaks (phaseInitialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion runtime leaks (phaseInitialLaw setup)
      horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    (completes : PhaseService.CompletesPlay runtime leaks (phaseInitialLaw setup)
      horizon scheduler)
    (phaseAssessments : ℕ → (M).BehavioralAssessment)
    (fallback : ℕ → ∀ who, (M).Policy who)
    (assembled : ∀ n, (phaseAssessments n).strategy =
      componentStrategy setup runtime leaks bounds horizon scheduler (fallback n) (sequence n)
        (scale n)
        (positive n).le (le_one n) (weights n))
    (mixed : ∀ n, (phaseAssessments n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (M) (phaseAssessments n)
      ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
        horizon
          scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ history :
      ((menu setup runtime leaks bounds).protocol (phaseInitialLaw setup) horizon
        scheduler).History,
      ∀ who, |phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (slots_pos : 0 < bounds.candidateCount)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :
    ∃ (score : ℕ → Option (LateKey (runtime := runtime) setup (RecoveryLeaks)) → LateOption
      bounds.candidateCount → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ score n key option ∧ score n key option ≤ 1) ∧
      ∀ n who (site : (M).InformationSite who) (clear : ClearInput setup runtime leaks site.1),
      ¬ FreeAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) →
      ¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds
        RecoveryPrior horizon
          (RecoveryScheduler)
        (projectedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) clear) →
      KeyedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) →
      ∃ nativeSite : (N).InformationSite who,
        nativeSite.1 = RecoveryProjection.information runtime (RecoveryLeaks)
          (projectInfo site.1) ∧
        excludedPayoff who ≤ siteValue (runtime := runtime) setup (RecoveryLeaks) bounds horizon
          (NativeScheduler)
            parameter
          utility excludedPayoff
          (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
            positive
            le_one weights n) (setup.intendedOpeningProfile (sequence n).strategy) nativeSite ∧
        ∀ option,
        |localValue (2 * horizon + 1) (fun final => final.state)
            (phaseExclusionBase setup .sequential runtime leaks
              (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
            (phaseAssessments n) site
            (keyedComponent setup runtime leaks bounds horizon scheduler (sequence n) (scale n)
              (positive n).le (le_one n) ((M).agentAt site) option) -
          (excludedPayoff who + score n
            (agentKey setup runtime leaks bounds horizon scheduler ((M).agentAt site)) option *
            (siteValue (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler)
              parameter utility
              excludedPayoff
              (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence
                scale positive
                le_one weights n) (setup.intendedOpeningProfile (sequence n).strategy) nativeSite -
              excludedPayoff who))| ≤ error n := by
  obtain ⟨failureScore, physical, physicalLimit, unit, valueNear⟩ :=
    nativeComparison_keyed_value_bounds setup runtime leaks bounds horizon scheduler opportunity
      inclusion
      timely completes wellFormed independent observable sequence sourceMixed scale positive le_one
      scaleEq covers coversInputs capacity slots_pos weights parameter utility excludedPayoff
      payoffBound nonnegative readoutBounded excludedBounded
  obtain ⟨transport, transportLimit, transported⟩ :=
    localValue_native_comparison_error_vanishes setup runtime
    leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed scale
    positive le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely
    rawCertificate certificate completes phaseAssessments fallback assembled mixed bayes parameter
    utility excludedPayoff nonnegative payoffBounded excludedBounded
  refine ⟨fun n key option => key.elim 0 (fun key => 1 - failureScore n key option),
    fun n => transport n + physical n, ?_, ?_, ?_⟩
  · simpa using transportLimit.add physicalLimit
  · intro n key option
    cases key with
    | none => exact ⟨le_rfl, zero_le_one⟩
    | some key =>
        change 0 ≤ 1 - failureScore n key option ∧ 1 - failureScore n key option ≤ 1
        have := unit n key option
        constructor <;> linarith
  intro n who site clear notFree notOwing keyed
  obtain ⟨past, view, event, key, atSite, turn, siteKey⟩ :=
    keyed_information setup runtime leaks bounds horizon scheduler site keyed
  have viewClear : view.application.2.excluded = ∅ := by
    rw [atSite] at clear
    exact clear
  obtain ⟨nativeSite, lifted, input, nativeNotFree, nativeNotOwing, localNear⟩ :=
    transported n who site past view atSite viewClear notFree notOwing event turn
  have nativeKeyed : ownedKeyed
      (Vegas.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler))
      (LateDeliveryAgent (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw
        setup) horizon
          (NativeScheduler))
      ((N).agentAt nativeSite) := by
    refine ⟨?_, nativeNotFree⟩
    change LateDelivery (runtime := runtime) setup (RecoveryLeaks) who nativeSite.1
    rw [input]
    exact keyed
  have lower := (siteValue_mem_Icc (runtime := runtime) setup (RecoveryLeaks) bounds horizon
    (NativeScheduler) parameter
    utility excludedPayoff
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
      weights n) (setup.intendedOpeningProfile (sequence n).strategy) nativeSite (upper who)
    (fun outcome => le_upper outcome who)
    (fun point reached => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
      wellFormed below (sequence n).strategy point reached who)).1
  refine ⟨nativeSite, input, lower, ?_⟩
  intro option
  have nativeKey : lateKey (runtime := runtime) setup (RecoveryLeaks) who nativeSite.1 = some key
    := by
    rw [input]
    exact siteKey
  have bridge := localNear (keyedComponent setup runtime leaks bounds horizon scheduler (sequence n)
    (scale n) (positive n).le (le_one n) ((M).agentAt site) option)
  have comparison := valueNear n who nativeSite nativeNotFree nativeNotOwing nativeKeyed key
    nativeKey option
  have lawEq := keyedComponent_native_choice setup runtime leaks bounds horizon scheduler
    (sequence n)
    (scale n) (positive n).le (le_one n) site clear nativeSite lifted option
  dsimp only at bridge comparison
  rw [lawEq] at bridge
  rw [siteKey]
  exact (abs_sub_le _ _ _).trans (add_le_add bridge comparison)

end Vegas.SequentialPhase
