/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeGainError
import Vegas.Game.SequentialPhaseUnpendingChoices
import Vegas.Game.SequentialPhaseNonLateNativeComparisons
import GameTheoryExtensions.Analysis.Protocol.GainComparison

/-! # Actual nonlate phase deviations compared with the original source gains -/

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
/-- Every pure nonlate actual phase deviation has a uniformly vanishing direct
bound or a lottery of original intended-game gains. The source sequence is fixed,
and unpending choices have exactly zero gain. -/
theorem nonlate_local_comparisons [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
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
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (M).InformationSite who) (clear : ClearInput setup runtime leaks site.1),
        ¬ FreeAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) →
        ¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds
          RecoveryPrior horizon
            (RecoveryScheduler)
          (projectedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) clear) →
        ¬ ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
          (KeyedAgent setup runtime leaks bounds horizon scheduler) ((M).agentAt site) →
        ∀ choice : (M).Choice who site.1,
          GainComparison
            (localGain (2 * horizon + 1) (fun final => final.state)
              (phaseExclusionBase setup .sequential runtime leaks
                (fun terminal => utility (setup.parameterOutcome parameter terminal))
                excludedPayoff)
              (phaseAssessments n) site (PMF.pure choice))
            (intendedSiteGain setup parameter utility excludedPayoff (sequence n) (who := who))
            (error n) := by
  classical
  let certificate := ((NMenu).bounded (Vegas.initialLaw setup) horizon
    (NativeScheduler)).wellFoundedHistories
  obtain ⟨nativeError, nativeLimit, nativeComparisons⟩ :=
    nativeComparison_nonlate_pending_comparisons setup runtime leaks bounds horizon scheduler
      opportunity
      inclusion timely completes wellFormed independent observable covers coversInputs capacity
      sequence sourceMixed sourceBayes scale positive le_one scaleEq weights parameter utility
      excludedPayoff below upper le_upper nonnegative readoutBounded excludedBounded
  obtain ⟨valueError, valueLimit, comparisons⟩ := localGain_native_comparison_error_vanishes setup
    runtime
    leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed scale
    positive le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely
    rawCertificate certificate completes phaseAssessments fallback assembled mixed bayes parameter
    utility excludedPayoff nonnegative payoffBounded excludedBounded
  let error := fun n => |nativeError n| + 2 * |valueError n|
  have limit : Tendsto error atTop (nhds 0) := by
    simpa only [error, abs_zero, mul_zero, add_zero] using
      nativeLimit.abs.add (valueLimit.abs.const_mul 2)
  refine ⟨error, limit, ?_⟩
  intro n who site clear notFree notOwing notKeyed choice
  have nonlate : ¬ KeyedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) :=
    fun keyed => notKeyed ⟨keyed, notFree⟩
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    cases infoEq : site.1 with
    | none => simp only [ClearInput, infoEq, Option.elim_none] at clear
    | some pair => exact ⟨pair.1, pair.2, rfl⟩
  have empty : view.application.2.excluded = ∅ := by
    simpa only [ClearInput, atSite, Option.elim_some] using clear
  let nativeInfo := RecoveryProjection.information runtime (RecoveryLeaks) (projectInfo
      site.1)
  cases pending : pendingEvent (runtime := runtime) setup (RecoveryLeaks) who nativeInfo with
  | none =>
    have zero := localGain_eq_zero_of_unpending_notOwing setup runtime leaks bounds horizon
      scheduler
      wellFormed site clear notFree notOwing nonlate past view atSite pending (2 * horizon + 1)
      (fun final => final.state) (phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
      (phaseAssessments n) (PMF.pure choice)
    exact Or.inl (by rw [zero]; dsimp only [error]; positivity)
  | some event =>
    have pendingAt := pending
    dsimp only [nativeInfo] at pendingAt
    rw [atSite] at pendingAt
    have turn : view.application.1.publicView.ownTurn? who = some event :=
      (pendingEvent_spec (runtime := runtime) pendingAt).1
    obtain ⟨nativeSite, lifted, input, nativeNotFree, nativeNotOwing, gains⟩ :=
      comparisons n who site past view atSite empty notFree notOwing event turn
    have nativeNonlate : ¬ LateDelivery (runtime := runtime) setup (RecoveryLeaks) who
      nativeSite.1 := by
      rw [input]
      exact nonlate
    have nativePending : pendingEvent (runtime := runtime) setup (RecoveryLeaks) who nativeSite.1
      = some event := by
      rw [input]
      exact pending
    let nativeChoice := RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup
      (RecoveryLeaks) bounds
        horizon
      (RecoveryScheduler) who nativeSite.1 (Equiv.cast
        (congrArg (fun info => (R).Choice who info) lifted.symm)
        (choiceEquiv setup runtime leaks bounds horizon scheduler ((M).agentAt site) clear choice))
    let native := nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence
      scale
      positive le_one weights n
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState (runtime := runtime) setup (RecoveryLeaks) (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase (runtime := runtime) setup parameter utility excludedPayoff (RecoveryLeaks)
        final.state who
    let nativeValue := fun law : PMF ((N).Choice who nativeSite.1) =>
      expect (native.belief who nativeSite) (fun history =>
        expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) native.strategy who
          ((native.strategy who).withLaw nativeSite.1 law)) stopped history.1) payoff)
    have gainBound := gains (PMF.pure choice)
    dsimp only at gainBound
    simp only [PMF.pure_map] at gainBound
    change localGain (2 * horizon + 1) (fun final => final.state)
      (phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
      (phaseAssessments n) site (PMF.pure choice) ≤ nativeValue (PMF.pure nativeChoice) -
        nativeValue (native.strategy who nativeSite.1) + 2 * valueError n at gainBound
    have baseline : nativeValue (native.strategy who nativeSite.1) =
        expect (native.belief who nativeSite) (fun history =>
          expect ((N).runBehavioralUntil certificate native.strategy stopped history.1)
            payoff) := by
      simp only [nativeValue, BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self]
    have gainEq : nativeValue (PMF.pure nativeChoice) -
        nativeValue (native.strategy who nativeSite.1) =
      expect (native.belief who nativeSite) (fun history =>
        expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) native.strategy who
            ((native.strategy who).withLaw nativeSite.1 (PMF.pure nativeChoice))) stopped history.1)
          payoff - expect ((N).runBehavioralUntil certificate native.strategy stopped history.1)
            payoff) := by
      rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
      exact congrArg (fun value => nativeValue (PMF.pure nativeChoice) - value) baseline
    have compared := nativeComparisons n who nativeSite nativeChoice nativeNotFree nativeNotOwing
      nativeNonlate nativePending
    dsimp only at compared
    rw [← gainEq] at compared
    have covered : nativeError n + 2 * valueError n ≤ error n := by
      dsimp only [error]
      linarith [le_abs_self (nativeError n), le_abs_self (valueError n)]
    rcases compared with direct | ⟨deviation, sourceBound⟩
    · exact Or.inl (by linarith only [gainBound, direct, covered])
    · refine Or.inr ⟨PMF.pure deviation, ?_⟩
      rw [expect_pure]
      linarith only [gainBound, sourceBound, covered]

end Vegas.SequentialPhase
