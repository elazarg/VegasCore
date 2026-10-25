/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryForeignExitBounds

/-! # Vanishing recovery continuation error under the common assessment -/

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

variable {Public : Type*} {signal : State L setup.context → Public}

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
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks


open Classical in
/-- Uniformly over all clear forced debt-free source-turn sites and all focal
recovery continuation policies, the original common assessment's expected
absolute terminal-payoff error against its concrete native debt-stopped law
vanishes. The continuation and belief use the unchanged completion weights. -/
theorem recovery_common_continuation_error_vanishes [Fintype (RP).History]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
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
        ∀ {past : List (recoveryApplication (runtime setup) leaks).PlayerEntry}
          {view : (recoveryApplication (runtime setup) leaks).PlayerView},
        site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        ∀ alternative : (R).BehavioralPolicy who,
        let updated := Profile.update (sig := (R).behavioralSignature)
          (assessments n).strategy who alternative
        let kernel := nativeDebtStoppedLaw setup leaks bounds horizon scheduler rawCertificate
          updated who
        let read := Sum.elim (fun _ : Finset Player => excludedPayoff who)
          (fun final : (RawNative).History =>
            if DecodedState setup leaks (failureProfile setup.program)
                (ProtocolState.OwesFailure who setup.program) final.state then excludedPayoff who
            else exclusionBase setup parameter utility excludedPayoff leaks final.state who)
        expect (((assessments n).belief who site).map Subtype.val) (fun history =>
          |expect ((R).runBehavioralTerminalFrom menuCertificate updated history)
              (fun final =>
                recoveryExclusionBase parameter utility excludedPayoff final.state who) -
            expect (kernel history) read|) ≤ error n := by
  obtain ⟨foreign, limit, foreignBound⟩ := recovery_common_foreign_exit_bounds setup leaks bounds
    horizon scheduler wellFormed independent observable sequence sourceMixed scale positive
    le_one scaleEq
      covers coversInputs capacity weights assessments fallback assembled bayes opportunity
        inclusion timely certificate rawCertificate
  refine ⟨fun n => (2 * payoffBound) * foreign n, ?_, ?_⟩
  · simpa only [mul_zero] using limit.const_mul (2 * payoffBound)
  intro n who site notFree notOwing past view atSite event turn alternative updated kernel read
  have controlled := belief_controlled_clear_of_notFree setup leaks bounds horizon scheduler
    (assessments n) site notFree
  have estimate := recovery_belief_expect_abs_sub_native_debt_stopped_le_foreign_exit setup leaks
    bounds horizon scheduler parameter utility excludedPayoff payoffBound nonnegative rawCertificate
      recoveryCertificate menuCertificate completes updated who (payoffBounded who)
        (excludedBounded who) (((assessments n).belief who site).map Subtype.val) controlled
  exact estimate.trans (mul_le_mul_of_nonneg_left
    (foreignBound n who site notFree notOwing atSite turn alternative) (by positivity))

end Vegas.RecoveryOnePacket
