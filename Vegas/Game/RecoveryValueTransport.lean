/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryContinuationLimit

/-! # Actual recovery gains and their common native stopped values -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

open Classical in
/-- Expected utility of the existing concrete native debt-stopped law. -/
def nativeDebtStoppedValue {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (certificate : (RawNative).WellFoundedHistories)
    (profile : ∀ who, (R).BehavioralPolicy who) (focal : Player) (history : (RP).History) : ℝ :=
  expect (nativeDebtStoppedLaw setup leaks bounds horizon scheduler certificate profile focal
    history)
    (Sum.elim (fun _ : Finset Player => excludedPayoff focal)
      (fun final : (RawNative).History =>
        if DecodedState setup leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure focal setup.program) final.state then excludedPayoff focal
        else exclusionBase setup parameter utility excludedPayoff leaks final.state focal))

open Classical in
/-- The original recovery assessment's local gain is bounded by the gain in its
concrete common native stopped laws, uniformly over full focal policies. -/
theorem recovery_common_gain_le_native_debt_stopped [Fintype (RP).History]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    (assessments : ℕ → (R).BehavioralAssessment)
    (fallback : ℕ → ∀ player, (R).Policy player)
    (assembled : ∀ n, (assessments n).strategy = (R).agentBehavior (R).playedInformation
      (fallback n)
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (R) (assessments n)
      ((RMenu).decisionInformationAntichain Initial horizon scheduler))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate : ((NMenu).protocol (initialLaw setup) horizon
      (NativeScheduler)).WellFoundedHistories)
    (rawCertificate : (RawNative).WellFoundedHistories)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (recoveryCertificate : ((recoveryApplication (runtime setup) leaks).protocol Initial horizon
      scheduler).WellFoundedHistories)
    (menuCertificate : (RP).WellFoundedHistories)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (payoffBounded : ∀ who (final : (RP).History),
      |recoveryExclusionBase parameter utility excludedPayoff final.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ∀ {past : List (RApp).PlayerEntry} {view : (RApp).PlayerView},
        site.1 = some (past, view) → ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        ∀ alternative : (R).BehavioralPolicy who,
        ((assessments n).continuationContext menuCertificate site
            (fun final => recoveryExclusionBase parameter utility excludedPayoff
              final.state who)).value
              alternative -
          ((assessments n).continuationContext menuCertificate site
            (fun final => recoveryExclusionBase parameter utility excludedPayoff
              final.state who)).value
              ((assessments n).strategy who) ≤
          expect (((assessments n).belief who site).map Subtype.val) (fun history =>
            nativeDebtStoppedValue setup leaks bounds horizon scheduler parameter utility
                excludedPayoff rawCertificate
                (Profile.update (sig := (R).behavioralSignature) (assessments n).strategy who
                  alternative) who history -
              nativeDebtStoppedValue setup leaks bounds horizon scheduler parameter utility
                excludedPayoff rawCertificate (assessments n).strategy who history) + error n := by
  obtain ⟨gap, limit, bounded⟩ := recovery_common_continuation_error_vanishes setup leaks bounds
    horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one scaleEq
      covers coversInputs capacity weights assessments fallback assembled bayes opportunity
        inclusion
        timely certificate rawCertificate parameter utility excludedPayoff payoffBound nonnegative
          recoveryCertificate menuCertificate completes payoffBounded excludedBounded
  refine ⟨fun n => 2 * gap n, ?_, ?_⟩
  · simpa only [mul_zero] using limit.const_mul 2
  intro n who site notFree notOwing past view atSite event turn alternative
  let belief := ((assessments n).belief who site).map Subtype.val
  let payoff := fun final : (RP).History =>
    recoveryExclusionBase parameter utility excludedPayoff final.state who
  let actual := fun policy : (R).BehavioralPolicy who => fun history : (RP).History =>
    expect ((R).runBehavioralTerminalFrom menuCertificate
      (Profile.update (sig := (R).behavioralSignature) (assessments n).strategy who policy) history)
      payoff
  let native := fun policy : (R).BehavioralPolicy who =>
    nativeDebtStoppedValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
      rawCertificate
      (Profile.update (sig := (R).behavioralSignature) (assessments n).strategy who policy) who
  have near (policy : (R).BehavioralPolicy who) :
      expect belief (fun history => |actual policy history - native policy history|) ≤ gap n :=
    bounded n who site notFree notOwing atSite turn policy
  have value (policy : (R).BehavioralPolicy who) :
      ((assessments n).continuationContext menuCertificate site payoff).value policy =
        expect belief (actual policy) := by
    rw [BehavioralAssessment.continuationContext_value, expect_bind_of_finite, expect_map]
    rfl
  have alternativeBound : expect belief (actual alternative) - expect belief (native alternative) ≤
      gap n := by
    rw [← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
    exact (expect_mono (fun history _ => le_abs_self _) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)).trans (near alternative)
  have baselineBound : expect belief (native ((assessments n).strategy who)) -
      expect belief (actual ((assessments n).strategy who)) ≤ gap n := by
    rw [← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
    exact (expect_mono (fun history _ => by
      simpa only [neg_sub] using neg_le_abs
        (actual ((assessments n).strategy who) history -
          native ((assessments n).strategy who) history)) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)).trans (near ((assessments n).strategy who))
  change ((assessments n).continuationContext menuCertificate site payoff).value alternative -
      ((assessments n).continuationContext menuCertificate site payoff).value
        ((assessments n).strategy who) ≤ _
  rw [value, value]
  have nativeDifference : expect belief (fun history =>
      native alternative history - native ((assessments n).strategy who) history) =
      expect belief (native alternative) - expect belief (native ((assessments n).strategy who)) :=
    expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  simpa only [native, Profile.update_eq_self] using
    (show expect belief (actual alternative) -
        expect belief (actual ((assessments n).strategy who)) ≤
      expect belief (fun history => native alternative history -
        native ((assessments n).strategy who) history) + 2 * gap n by
      rw [nativeDifference]
      linarith)

end Vegas.RecoveryOnePacket
