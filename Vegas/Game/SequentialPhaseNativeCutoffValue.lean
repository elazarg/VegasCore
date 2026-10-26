/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeInformation
import Vegas.Game.RecoveryLocalStoppedValue

/-! # Exact comparison cutoff values under the native information fiber -/

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

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

open Classical in
/-- The actual recovery comparison's debt-stopped Bayesian value is exactly
its assembled native comparison value, retaining one fixed site for every local law. -/
theorem recovery_bayes_debt_stopped_eq_native
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (n : ℕ) (who : Player) (site : (R).InformationSite who)
    (notFree : ¬ RecoveryOnePacket.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds
      RecoveryPrior horizon
        (RecoveryScheduler)
      ((R).agentAt site))
    (notOwing : ¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds
      RecoveryPrior horizon
      (RecoveryScheduler)
      ((R).agentAt site))
    (recoveryPositive : 0 < (R).informationMass
      (recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler (source n) (scale n)
        (positive n).le (le_one n) (weights n)) who site)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    ∃ (nativeSite : (N).InformationSite who)
      (lifted : RecoveryProjection.liftInformation runtime (RecoveryLeaks) nativeSite.1 =
        site.1),
      nativeSite.1 = RecoveryProjection.information runtime (RecoveryLeaks) site.1 ∧
      ¬ Vegas.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon
        (NativeScheduler) ((N).agentAt
          nativeSite) ∧
      ¬ Vegas.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler)
        ((N).agentAt nativeSite) ∧
      ∀ law : PMF ((R).Choice who site.1),
      let localLaw := (law.map (Equiv.cast
        (congrArg (fun input => (R).Choice who input) lifted.symm))).map
          (RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup (RecoveryLeaks)
            bounds horizon
              (RecoveryScheduler)
            who nativeSite.1)
      let recoveryProfile := recoveryComparisonStrategy setup runtime leaks bounds horizon
        scheduler (source
          n)
        (scale n) (positive n).le (le_one n) (weights n)
      let updated := Profile.update (sig := (R).behavioralSignature) recoveryProfile who
        ((recoveryProfile who).withLaw site.1 law)
      let stopped := fun final : (NP).History => ¬ Clear final.state ∨
        DecodedState (runtime := runtime) setup (RecoveryLeaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state
      expect ((R).bayesBelief recoveryProfile who site
          ((RMenu).decisionInformationAntichain RecoveryPrior horizon (RecoveryScheduler) who site)
          recoveryPositive)
          (fun history => RecoveryOnePacket.nativeDebtStoppedValue (runtime := runtime) setup
            (RecoveryLeaks) bounds
              horizon
            (RecoveryScheduler) parameter utility excludedPayoff rawCertificate updated who
                history.1) =
        expect ((nativeComparisonSequence setup runtime leaks bounds horizon scheduler source
          scale positive
          le_one weights n).belief who nativeSite) (fun history =>
            expect ((N).runBehavioralUntil certificate
              (Profile.update (sig := (N).behavioralSignature)
                (nativeComparisonSequence setup runtime leaks bounds horizon scheduler source
                  scale positive
                  le_one weights n).strategy who
                (((nativeComparisonSequence setup runtime leaks bounds horizon scheduler source
                  scale
                  positive le_one weights n).strategy who).withLaw nativeSite.1 localLaw)) stopped
                history.1)
              (fun final => if stopped final then excludedPayoff who else
                exclusionBase (runtime := runtime) setup parameter utility excludedPayoff
                  (RecoveryLeaks) final.state
                    who)) :=
    by
  obtain ⟨nativeSite, project, nativeInput, nativeNotFree, nativeNotOwing, raw, _states, beliefs⟩ :=
    exists_native_comparison_information setup runtime leaks bounds horizon scheduler source scale
      positive
      le_one weights n who site notFree notOwing
  have lifted : RecoveryProjection.liftInformation runtime (RecoveryLeaks) nativeSite.1 =
      site.1 := by
    rw [nativeInput]
    exact (Classical.not_not.mp notFree).1
  refine ⟨nativeSite, lifted, nativeInput, nativeNotFree, nativeNotOwing, ?_⟩
  rcases site with ⟨input, decision⟩
  dsimp only at lifted
  cases lifted
  intro law localLaw recoveryProfile updated stopped
  have localLawEq : localLaw = law.map
      (RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup (RecoveryLeaks) bounds
        horizon
          (RecoveryScheduler)
        who nativeSite.1) := by
    change (law.map id).map _ = _
    rw [PMF.map_id]
  have beliefEq : (recoveryComparisonSequence setup runtime leaks bounds horizon scheduler source
    scale
      positive le_one weights n).belief who ⟨_, decision⟩ =
      (R).bayesBelief recoveryProfile who ⟨_, decision⟩
        ((RMenu).decisionInformationAntichain RecoveryPrior horizon (RecoveryScheduler) who ⟨_,
            decision⟩)
        recoveryPositive := by
    exact (BehavioralAssessment.isBayesConsistentAt_iff (R)
      (recoveryComparisonSequence setup runtime leaks bounds horizon scheduler source scale
        positive le_one
        weights n) who ⟨_, decision⟩
      ((RMenu).decisionInformationAntichain RecoveryPrior horizon (RecoveryScheduler) who ⟨_,
          decision⟩)
      recoveryPositive).mp ((recoveryComparisonSequence_bayes setup runtime leaks bounds horizon
        scheduler
          source
        scale positive le_one weights n) who ⟨_, decision⟩ recoveryPositive)
  rw [← beliefEq, ← beliefs, expect_map]
  apply expect_congr_on_support
  intro history _supported
  obtain ⟨clear, same⟩ := raw history
  have historyEq := RecoveryOnePacket.nativeClearHistory_eq_of_raw (runtime := runtime) setup
    (RecoveryLeaks) bounds
      horizon
    (RecoveryScheduler) history.1 clear (project history).1 same
  have bridge := RecoveryOnePacket.nativeDebtStoppedValue_localLaw_eq_comparison (runtime :=
    runtime) setup
      (RecoveryLeaks)
    bounds horizon (RecoveryScheduler) source scale positive le_one
    (fun n => recoveryComparisonWeights setup runtime leaks bounds horizon scheduler (weights n)) n
    (recoveryComparisonFallback setup runtime leaks bounds horizon scheduler) recoveryProfile rfl
      parameter
    utility
    excludedPayoff rawCertificate certificate who nativeSite.1 law history.1 clear
  rw [historyEq] at bridge
  rw [localLawEq]
  exact bridge

end Vegas.SequentialPhase
