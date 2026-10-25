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
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "Initial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (oldLeaks)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) Initial horizon
  (oldScheduler)
local notation "NP" => onePacketProtocol setup (oldLeaks) bounds horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup (oldLeaks))
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application setup (oldLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local instance cutoffComparisonHistory : Fintype ((RMenu).protocol
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).History :=
  sourceHistoryFintype setup leaks bounds horizon scheduler

local instance cutoffComparisonInformation (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds
      ((Vegas.initialLaw setup).map (fun native =>
        (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).InfoState who) :=
  sourceInfoDecidableEq setup leaks bounds horizon scheduler who

local instance cutoffComparisonNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance cutoffNativeInformation (who : Player) : DecidableEq ((N).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

local instance cutoffRecoveryNature :
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) (oldScheduler) :=
  recoveryNature setup leaks scheduler

local instance cutoffNativeHistory : Fintype (NP).History :=
  @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (NMenu) (Vegas.initialLaw setup)
    horizon (NativeScheduler) inferInstance (nativeNature setup leaks scheduler)

open Classical in
/-- The actual recovery comparison's debt-stopped Bayesian value is exactly
its assembled native comparison value, retaining one fixed site for every local law. -/
theorem recovery_bayes_debt_stopped_eq_native
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (n : ℕ) (who : Player) (site : (R).InformationSite who)
    (notFree : ¬ RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds Initial horizon (oldScheduler)
      ((R).agentAt site))
    (notOwing : ¬ RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler)
      ((R).agentAt site))
    (oldPositive : 0 < (R).informationMass
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler (source n) (scale n)
        (positive n).le (le_one n) (weights n)) who site)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    ∃ (nativeSite : (N).InformationSite who)
      (lifted : RecoveryProjection.liftInformation (runtime setup) (oldLeaks) nativeSite.1 =
        site.1),
      nativeSite.1 = RecoveryProjection.information (runtime setup) (oldLeaks) site.1 ∧
      ¬ Vegas.FreeAgent setup (oldLeaks) bounds horizon (NativeScheduler) ((N).agentAt nativeSite) ∧
      ¬ Vegas.OwingAgent setup (oldLeaks) bounds horizon (NativeScheduler)
        ((N).agentAt nativeSite) ∧
      ∀ law : PMF ((R).Choice who site.1),
      let localLaw := (law.map (Equiv.cast
        (congrArg (fun input => (R).Choice who input) lifted.symm))).map
          (RecoveryOnePacket.sourceNativeChoiceEquiv setup (oldLeaks) bounds horizon (oldScheduler)
            who nativeSite.1)
      let oldProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler (source n)
        (scale n) (positive n).le (le_one n) (weights n)
      let updated := Profile.update (sig := (R).behavioralSignature) oldProfile who
        ((oldProfile who).withLaw site.1 law)
      let stopped := fun final : (NP).History => ¬ Clear final.state ∨
        DecodedState setup (oldLeaks) (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state
      expect ((R).bayesBelief oldProfile who site
          ((RMenu).decisionInformationAntichain Initial horizon (oldScheduler) who site)
          oldPositive)
          (fun history => RecoveryOnePacket.nativeDebtStoppedValue setup (oldLeaks) bounds horizon
            (oldScheduler) parameter utility excludedPayoff rawCertificate updated who history.1) =
        expect ((nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive
          le_one weights n).belief who nativeSite) (fun history =>
            expect ((N).runBehavioralUntil certificate
              (Profile.update (sig := (N).behavioralSignature)
                (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive
                  le_one weights n).strategy who
                (((nativeComparisonSequence setup leaks bounds horizon scheduler source scale
                  positive le_one weights n).strategy who).withLaw nativeSite.1 localLaw)) stopped
                history.1)
              (fun final => if stopped final then excludedPayoff who else
                exclusionBase setup parameter utility excludedPayoff (oldLeaks) final.state who)) :=
    by
  obtain ⟨nativeSite, project, nativeInput, nativeNotFree, nativeNotOwing, raw, _states, beliefs⟩ :=
    exists_native_comparison_information setup leaks bounds horizon scheduler source scale positive
      le_one weights n who site notFree notOwing
  have lifted : RecoveryProjection.liftInformation (runtime setup) (oldLeaks) nativeSite.1 =
      site.1 := by
    rw [nativeInput]
    exact (Classical.not_not.mp notFree).1
  refine ⟨nativeSite, lifted, nativeInput, nativeNotFree, nativeNotOwing, ?_⟩
  rcases site with ⟨input, decision⟩
  dsimp only at lifted
  cases lifted
  intro law localLaw oldProfile updated stopped
  have localLawEq : localLaw = law.map
      (RecoveryOnePacket.sourceNativeChoiceEquiv setup (oldLeaks) bounds horizon (oldScheduler)
        who nativeSite.1) := by
    change (law.map id).map _ = _
    rw [PMF.map_id]
  have beliefEq : (recoveryComparisonSequence setup leaks bounds horizon scheduler source scale
      positive le_one weights n).belief who ⟨_, decision⟩ =
      (R).bayesBelief oldProfile who ⟨_, decision⟩
        ((RMenu).decisionInformationAntichain Initial horizon (oldScheduler) who ⟨_, decision⟩)
        oldPositive := by
    exact (BehavioralAssessment.isBayesConsistentAt_iff (R)
      (recoveryComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
        weights n) who ⟨_, decision⟩
      ((RMenu).decisionInformationAntichain Initial horizon (oldScheduler) who ⟨_, decision⟩)
      oldPositive).mp ((recoveryComparisonSequence_bayes setup leaks bounds horizon scheduler source
        scale positive le_one weights n) who ⟨_, decision⟩ oldPositive)
  rw [← beliefEq, ← beliefs, expect_map]
  apply expect_congr_on_support
  intro history _supported
  obtain ⟨clear, same⟩ := raw history
  have historyEq := RecoveryOnePacket.nativeClearHistory_eq_of_raw setup (oldLeaks) bounds horizon
    (oldScheduler) history.1 clear (project history).1 same
  have bridge := RecoveryOnePacket.nativeDebtStoppedValue_localLaw_eq_comparison setup (oldLeaks)
    bounds horizon (oldScheduler) source scale positive le_one
    (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)) n
    (recoveryComparisonFallback setup leaks bounds horizon scheduler) oldProfile rfl parameter
    utility
    excludedPayoff rawCertificate certificate who nativeSite.1 law history.1 clear
  rw [historyEq] at bridge
  rw [localLawEq]
  exact bridge

end Vegas.SequentialPhase
