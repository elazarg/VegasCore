/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeValueError
import Vegas.Game.SequentialPhaseNativeStrategyLaw

/-! # Original phase local gains against the actual native comparison baseline -/

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
/-- Original phase local gains are bounded by the actual native cutoff gain
plus twice the uniform value error. The same native site and actual native
strategy baseline serve every local law. -/
theorem localGain_native_comparison_error_vanishes [Finite setup.intendedProtocol.History]
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
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (M).InformationSite who)
        (past : List (P).PlayerEntry) (view : (P).PlayerView)
        (atSite : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅),
      let agent := (M).agentAt site
      let agentClear : ClearInput setup runtime leaks agent.2.1 := by
        change ClearInput setup runtime leaks site.1
        rw [atSite]
        exact clear
      ¬ FreeAgent setup runtime leaks bounds horizon scheduler agent →
      ¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds
        RecoveryPrior horizon
          (RecoveryScheduler)
        (projectedAgent setup runtime leaks bounds horizon scheduler agent agentClear) →
      ∀ event : (graph setup).EventId,
        view.application.1.publicView.ownTurn? who = some event →
      ∃ (nativeSite : (N).InformationSite who)
        (lifted : RecoveryProjection.liftInformation runtime (RecoveryLeaks) nativeSite.1 =
          projectInfo site.1),
        nativeSite.1 = RecoveryProjection.information runtime (RecoveryLeaks)
          (projectInfo site.1) ∧
        ¬ Vegas.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon
          (NativeScheduler)
          ((N).agentAt nativeSite) ∧
        ¬ Vegas.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon
          (NativeScheduler)
          ((N).agentAt nativeSite) ∧
        let native := nativeComparisonSequence setup runtime leaks bounds horizon scheduler
          sequence scale
          positive le_one weights n
        let stopped := fun final : (NP).History => ¬ Clear final.state ∨
          DecodedState (runtime := runtime) setup (RecoveryLeaks) (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        let cutoffValue := fun law : PMF ((N).Choice who nativeSite.1) =>
          expect (native.belief who nativeSite) (fun history =>
            expect ((N).runBehavioralUntil certificate
              (Profile.update (sig := (N).behavioralSignature) native.strategy who
                ((native.strategy who).withLaw nativeSite.1 law)) stopped history.1)
              (fun final => if stopped final then excludedPayoff who else
                exclusionBase (runtime := runtime) setup parameter utility excludedPayoff
                  (RecoveryLeaks) final.state
                    who))
        ∀ law : PMF ((M).Choice who site.1),
        let localLaw := ((law.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent
          agentClear)).map (Equiv.cast
            (congrArg (fun input => (R).Choice who input) lifted.symm))).map
          (RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup (RecoveryLeaks)
            bounds horizon
              (RecoveryScheduler)
            who nativeSite.1)
        localGain (2 * horizon + 1) (fun final => final.state)
            (phaseExclusionBase setup .sequential runtime leaks
              (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
            (phaseAssessments n) site law ≤
          cutoffValue localLaw - cutoffValue (native.strategy who nativeSite.1) + 2 * error n := by
  obtain ⟨error, limit, bounded⟩ := localValue_native_comparison_error_vanishes setup runtime
    leaks bounds
    horizon scheduler wellFormed independent observable sequence sourceMixed scale positive le_one
    scaleEq covers coversInputs capacity weights opportunity inclusion timely rawCertificate
    certificate completes phaseAssessments fallback assembled mixed bayes parameter utility
    excludedPayoff nonnegative payoffBounded excludedBounded
  refine ⟨error, limit, ?_⟩
  intro n who site past view atSite clear agent agentClear notFree notOwing event turn
  obtain ⟨nativeSite, lifted, nativeInput, nativeNotFree, nativeNotOwing, values⟩ :=
    bounded n who site past view atSite clear notFree notOwing event turn
  refine ⟨nativeSite, lifted, nativeInput, nativeNotFree, nativeNotOwing, ?_⟩
  intro native stopped cutoffValue law localLaw
  have alternative := values law
  have baseline := values ((phaseAssessments n).strategy who site.1)
  have baselineLaw := phase_strategy_native_law setup runtime leaks bounds horizon scheduler
    sequence scale
    positive le_one weights n (fallback n) (phaseAssessments n) (assembled n) who site past view
    atSite clear nativeSite lifted
  dsimp only at alternative baseline baselineLaw
  erw [baselineLaw] at baseline
  change |localValue (2 * horizon + 1) (fun final => final.state)
    (phaseExclusionBase setup .sequential runtime leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
    (phaseAssessments n) site law - cutoffValue localLaw| ≤ error n at alternative
  change |localValue (2 * horizon + 1) (fun final => final.state)
    (phaseExclusionBase setup .sequential runtime leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
    (phaseAssessments n) site ((phaseAssessments n).strategy who site.1) -
      cutoffValue (native.strategy who nativeSite.1)| ≤ error n at baseline
  rw [localGain_eq_sub]
  linarith [(abs_le.mp alternative).2, (abs_le.mp baseline).1]

end Vegas.SequentialPhase
