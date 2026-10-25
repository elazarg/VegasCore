/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalValueError
import Vegas.Game.SequentialPhaseNativeCutoffValue

/-! # Original phase local values against one fixed actual native comparison site -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup)
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) (RecoveryLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (RecoveryLeaks)
local notation "N" => onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) RecoveryPrior horizon
  (RecoveryScheduler)
local notation "NP" => onePacketProtocol setup (RecoveryLeaks) bounds horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup (RecoveryLeaks))
  (PMF.map RecoveryState.native (RecoveryPrior)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application setup
    (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks
    (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

variable {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- Original phase local values have one fixed actual native comparison site
for every baseline and deviation law. The choice map retains the exact phase
menu equivalence, lifted-input cast and native menu equivalence; the original
payoff differs from its native cutoff value by a uniform error tending to zero. -/
theorem localValue_native_comparison_error_vanishes [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup (RecoveryLeaks) bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (phaseInitialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (phaseInitialLaw setup)
      horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (phaseInitialLaw setup)
      horizon scheduler)
    (phaseAssessments : ℕ → (M).BehavioralAssessment)
    (fallback : ℕ → ∀ who, (M).Policy who)
    (assembled : ∀ n, (phaseAssessments n).strategy =
      componentStrategy setup leaks bounds horizon scheduler (fallback n) (sequence n) (scale n)
        (positive n).le (le_one n) (weights n))
    (mixed : ∀ n, (phaseAssessments n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (M) (phaseAssessments n)
      ((menu setup leaks bounds).decisionInformationAntichain (phaseInitialLaw setup) horizon
          scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ history :
      ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History,
      ∀ who, |phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (M).InformationSite who)
        (past : List (P).PlayerEntry) (view : (P).PlayerView)
        (atSite : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅),
      let agent := (M).agentAt site
      let agentClear : ClearInput setup leaks agent.2.1 := by
        change ClearInput setup leaks site.1
        rw [atSite]
        exact clear
      ¬ FreeAgent setup leaks bounds horizon scheduler agent →
      ¬ RecoveryOnePacket.OwingAgent setup (RecoveryLeaks) bounds RecoveryPrior horizon
          (RecoveryScheduler)
        (projectedAgent setup leaks bounds horizon scheduler agent agentClear) →
      ∀ event : (graph setup).EventId,
        view.application.1.publicView.ownTurn? who = some event →
      ∃ (nativeSite : (N).InformationSite who)
        (lifted : RecoveryProjection.liftInformation (runtime setup) (RecoveryLeaks) nativeSite.1 =
          projectInfo site.1),
        nativeSite.1 = RecoveryProjection.information (runtime setup) (RecoveryLeaks)
          (projectInfo site.1) ∧
        ¬ Vegas.FreeAgent setup (RecoveryLeaks) bounds horizon (NativeScheduler)
          ((N).agentAt nativeSite) ∧
        ¬ Vegas.OwingAgent setup (RecoveryLeaks) bounds horizon (NativeScheduler)
          ((N).agentAt nativeSite) ∧
        ∀ law : PMF ((M).Choice who site.1),
        let localLaw := ((law.map (choiceEquiv setup leaks bounds horizon scheduler agent
          agentClear)).map (Equiv.cast
            (congrArg (fun input => (R).Choice who input) lifted.symm))).map
          (RecoveryOnePacket.sourceNativeChoiceEquiv setup (RecoveryLeaks) bounds horizon
              (RecoveryScheduler)
            who nativeSite.1)
        let stopped := fun final : (NP).History => ¬ Clear final.state ∨
          DecodedState setup (RecoveryLeaks) (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        |localValue (2 * horizon + 1) (fun final => final.state)
            (phaseExclusionBase setup .sequential (runtime setup) leaks
              (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
            (phaseAssessments n) site law -
          expect ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
            positive le_one weights n).belief who nativeSite) (fun history =>
            expect ((N).runBehavioralUntil certificate
              (Profile.update (sig := (N).behavioralSignature)
                (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
                  positive le_one weights n).strategy who
                (((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
                  positive le_one weights n).strategy who).withLaw nativeSite.1 localLaw)) stopped
                history.1)
              (fun final => if stopped final then excludedPayoff who else
                exclusionBase setup parameter utility excludedPayoff (RecoveryLeaks) final.state
                    who))| ≤
          error n := by
  obtain ⟨error, limit, bounded⟩ := localValue_native_error_vanishes setup leaks bounds horizon
    scheduler wellFormed independent observable sequence sourceMixed scale positive le_one scaleEq
    covers coversInputs capacity weights opportunity inclusion timely rawCertificate certificate
    completes phaseAssessments fallback assembled mixed bayes parameter utility excludedPayoff
    nonnegative payoffBounded excludedBounded
  refine ⟨error, limit, ?_⟩
  intro n who site past view atSite clear agent agentClear notFree notOwing event turn
  obtain ⟨recoverySite, recoveryPositive, recoveryInput, recoveryError⟩ := bounded n who site past
      view atSite clear
    notFree notOwing event turn
  have agentEq : (R).agentAt recoverySite =
      projectedAgent setup leaks bounds horizon scheduler agent agentClear := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext recoveryInput)
  have recoveryNotFree : ¬ RecoveryOnePacket.FreeAgent setup (RecoveryLeaks) bounds RecoveryPrior
      horizon
      (RecoveryScheduler) ((R).agentAt recoverySite) := by
    rw [agentEq]
    exact fun free => notFree ((freeAgent_projected_iff setup leaks bounds horizon scheduler
      agent agentClear).mp free)
  have recoveryNotOwing : ¬ RecoveryOnePacket.OwingAgent setup (RecoveryLeaks) bounds RecoveryPrior
      horizon
      (RecoveryScheduler) ((R).agentAt recoverySite) := by
    rw [agentEq]
    exact notOwing
  obtain ⟨nativeSite, lifted, nativeInput, nativeNotFree, nativeNotOwing, values⟩ :=
    recovery_bayes_debt_stopped_eq_native setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n who recoverySite recoveryNotFree recoveryNotOwing recoveryPositive
          rawCertificate
      certificate parameter utility excludedPayoff
  rcases recoverySite with ⟨recoveryInfo, recoveryDecision⟩
  change recoveryInfo = projectInfo site.1 at recoveryInput
  subst recoveryInfo
  refine ⟨nativeSite, lifted, nativeInput, nativeNotFree, nativeNotOwing, ?_⟩
  intro law localLaw stopped
  have transfer := values (law.map (choiceEquiv setup leaks bounds horizon scheduler agent
    agentClear))
  have near := recoveryError law
  dsimp only at near transfer
  rw [transfer] at near
  exact near

end Vegas.SequentialPhase
