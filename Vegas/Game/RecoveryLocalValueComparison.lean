/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryLocalStoppedValue

/-! # Local recovery values under the same comparison posterior -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication runtime leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup runtime leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native
    ∅))
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon (NativeScheduler)

open Classical in
/-- Every actual local recovery law has the same finite native comparison value,
up to the concrete vanishing recovery continuation error. The comparison retains
the original common weights and the full information-history posterior. -/
theorem recovery_local_value_comparison_bounds [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ player, DecidableEq ((N).InfoState player)]
    [(recoveryApplication runtime leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds Initial horizon scheduler bounds.candidateCount p))
    (assessments : ℕ → (R).BehavioralAssessment)
    (fallback : ℕ → ∀ player, (R).Policy player)
    (assembled : ∀ n, (assessments n).strategy = (R).agentBehavior (R).playedInformation
      (fallback n)
      (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler
        agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (R) (assessments n)
      ((RMenu).decisionInformationAntichain Initial horizon scheduler))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (certificate : ((NMenu).protocol (initialLaw setup) horizon
      (NativeScheduler)).WellFoundedHistories)
    (rawCertificate : (RawNative).WellFoundedHistories)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (recoveryCertificate : ((recoveryApplication runtime leaks).protocol Initial horizon
      scheduler).WellFoundedHistories)
    (menuCertificate : (RP).WellFoundedHistories)
    (completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler)
    (payoffBounded : ∀ who (final : (RP).History),
      |recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff final.state
        who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ∀ {past : List (RApp).PlayerEntry} {view : (RApp).PlayerView},
        site.1 = some (past, view) → ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        ∃ (nativeSite : (N).InformationSite who)
          (project : (R).InformationHistory who site.1 →
            (N).InformationHistory who nativeSite.1)
          (lifted : liftInformation runtime leaks nativeSite.1 = site.1),
          nativeSite.1 = RecoveryProjection.information runtime leaks site.1 ∧
          ¬ Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt
            nativeSite) ∧
          ¬ Vegas.OwingAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt
            nativeSite) ∧
          (∀ history, (project history).1.state =
            protocolState runtime leaks history.1.state) ∧
          ((assessments n).belief who site).map project =
            (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
              positive
              le_one weights n).belief who nativeSite ∧
          ∀ law : PMF ((R).Choice who site.1),
          let localLaw := (law.map (Equiv.cast
            (congrArg (fun input => (R).Choice who input) lifted.symm))).map
              (sourceNativeChoiceEquiv setup runtime leaks bounds horizon scheduler who
                nativeSite.1)
          let common := nativeComparisonStrategy setup runtime leaks bounds horizon scheduler
            sequence scale
            positive le_one weights n
          let stopped := fun final : (NP).History => ¬ ClearState final.state ∨
            DecodedState setup runtime leaks (failureProfile setup.program)
              (ProtocolState.OwesFailure who setup.program) final.state
          |localValue (2 * horizon + 1) (fun final => final.state)
              (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff)
                (assessments n) site law -
            expect ((nativeComparisonSequence setup runtime leaks bounds horizon scheduler
              sequence scale
              positive le_one weights n).belief who nativeSite) (fun history =>
                expect ((N).runBehavioralUntil certificate
                  (Profile.update (sig := (N).behavioralSignature) common who
                    ((common who).withLaw nativeSite.1 localLaw)) stopped history.1)
                    (fun final => if stopped final then excludedPayoff who else
                      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state
                        who))| ≤
            error n := by
  obtain ⟨error, limit, bounded⟩ := recovery_common_continuation_error_vanishes setup runtime
    leaks bounds
    horizon scheduler wellFormed independent observable sequence sourceMixed scale positive
    le_one scaleEq
    covers coversInputs capacity weights assessments fallback assembled bayes opportunity inclusion
    timely certificate rawCertificate parameter utility excludedPayoff payoffBound nonnegative
    recoveryCertificate menuCertificate completes payoffBounded excludedBounded
  refine ⟨error, limit, ?_⟩
  intro n who site notFree notOwing past view atSite event turn
  obtain ⟨nativeSite, project, input, nativeNotFree, nativeNotOwing, raw, states, lawEq⟩ :=
    exists_comparisonInformationHistory setup runtime leaks bounds horizon scheduler sequence
      scale positive
      le_one weights assessments fallback assembled bayes n who site notFree notOwing
  have lifted : liftInformation runtime leaks nativeSite.1 = site.1 := by
    rw [input]
    exact (Classical.not_not.mp notFree).1
  refine ⟨nativeSite, project, lifted, input, nativeNotFree, nativeNotOwing, states, lawEq, ?_⟩
  rcases site with ⟨input, decision⟩
  dsimp only at lifted
  cases lifted
  intro law localLaw common stopped
  have localLawEq : localLaw = law.map
      (sourceNativeChoiceEquiv setup runtime leaks bounds horizon scheduler who nativeSite.1) := by
    change (law.map id).map _ = _
    rw [PMF.map_id]
  let updated := Profile.update (sig := (R).behavioralSignature) (assessments n).strategy who
    (((assessments n).strategy who).withLaw (liftInformation runtime leaks nativeSite.1)
      law)
  let actual := fun history : (R).InformationHistory who
      (liftInformation runtime leaks nativeSite.1) =>
    expect ((R).runBehavioralTerminalFrom menuCertificate updated history.1)
      (fun final => recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff
        final.state who)
  let reference := fun history : (R).InformationHistory who
      (liftInformation runtime leaks nativeSite.1) =>
    nativeDebtStoppedValue setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff
      rawCertificate updated who history.1
  have near := bounded n who ⟨_, decision⟩ notFree notOwing atSite turn
    (((assessments n).strategy who).withLaw _ law)
  dsimp only at near
  rw [expect_map] at near
  have value : localValue (2 * horizon + 1) (fun final => final.state)
      (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff) (assessments
        n) ⟨_, decision⟩ law =
      expect ((assessments n).belief who ⟨_, decision⟩) actual := by
    rw [localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
      (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff) (assessments
        n) ⟨_, decision⟩
      ((RMenu).bounded Initial horizon scheduler), BehavioralAssessment.continuationContext_value,
      expect_bind_of_finite]
  have projected : expect ((nativeComparisonSequence setup runtime leaks bounds horizon scheduler
    sequence
      scale positive le_one weights n).belief who nativeSite) (fun history =>
        expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw nativeSite.1 localLaw)) stopped history.1)
          (fun final => if stopped final then excludedPayoff who else
            exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who)) =
      expect ((assessments n).belief who ⟨_, decision⟩) reference := by
    rw [← lawEq, expect_map]
    apply expect_congr_on_support
    intro history _supported
    obtain ⟨clear, same⟩ := raw history
    have historyEq := nativeClearHistory_eq_of_raw setup runtime leaks bounds horizon scheduler
      history.1
      clear (project history).1 same
    have bridge := nativeDebtStoppedValue_localLaw_eq_comparison setup runtime leaks bounds horizon
      scheduler sequence scale positive le_one weights n (fallback n) (assessments n).strategy
      (assembled n) parameter utility excludedPayoff rawCertificate certificate who nativeSite.1
      law history.1 clear
    rw [historyEq] at bridge
    rw [localLawEq]
    exact bridge.symm
  rw [value, projected]
  have difference := abs_expect_sub_le_expect ((assessments n).belief who ⟨_, decision⟩)
    actual reference (fun history => |actual history - reference history|) (fun _ _ => le_rfl)
  exact difference.trans near

end Vegas.RecoveryOnePacket
