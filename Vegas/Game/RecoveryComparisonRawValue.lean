/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryLocalStoppedValue
import Vegas.Game.RecoveryComparisonContinuationValue

/-! # Actual raw stopped values at intended source successor boundaries -/

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
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native Initial) horizon (NativeScheduler)

/-- The original common recovery strategy has the source continuation value at
every intended successor boundary, with one uniformly vanishing error for its
actual raw classified debt-stopped surrogate. -/
theorem recovery_common_boundary_value_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishing : Tendsto scale atTop (nhds 0)) {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p))
    (strategies : ℕ → ∀ who, (R).BehavioralPolicy who)
    (fallback : ℕ → ∀ who, (R).Policy who)
    (assembled : ∀ n, strategies n = (R).agentBehavior (R).playedInformation (fallback n)
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (history : (RP).History) (clear : ∀ current, history.state = some current →
        current.execution.application.excluded = ∅)
        (rank : Nat) (anchor : (application setup leaks).Execution),
        (nativeClearHistory setup leaks bounds horizon scheduler history clear).state =
            some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ →
        ReachedBoundary setup leaks horizon (NativeScheduler) rank anchor →
        ∀ point : ProtocolState setup.program,
        sourceServicePrefix? setup rank anchor.application.config = some point →
        ProtocolState.Intended setup.program point →
        |nativeDebtStoppedValue setup leaks bounds horizon scheduler parameter utility
            excludedPayoff rawCertificate (strategies n) who history -
          sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile (sequence n).strategy) who point| ≤ error n := by
  classical
  let error := fun n =>
    (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
      (2 * horizon + 1)
  refine ⟨error, ?_, ?_⟩
  · have difference := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_slotRetention vanishing)
    have limit := ((difference.const_mul (Fintype.card Player : ℝ)).const_mul
      (2 * payoffBound)).mul_const (2 * horizon + 1 : ℝ)
    simpa only [sub_self, mul_zero, zero_mul] using limit
  · intro n who history clear rank anchor state boundary point decoded intended
    rw [nativeDebtStoppedValue_eq_finite_continuation setup leaks bounds horizon scheduler
      parameter utility excludedPayoff rawCertificate certificate (strategies n) who history clear,
      ← nativeComparison_stopped_eq setup leaks bounds horizon scheduler sequence scale positive
        le_one weights n (fallback n) (strategies n) (assembled n) certificate
        (fun final => DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state)]
    have near := nativeComparison_stopped_boundary_value_sub_le setup leaks bounds horizon
      scheduler wellFormed covers capacity sequence scale positive le_one weights n opportunity
      inclusion timely completes certificate rank _ anchor state boundary point decoded intended
      parameter utility excludedPayoff who boundNonneg (readoutBounded who) (excludedBounded who)
    have depth : (application setup leaks).rank horizon
        (nativeClearHistory setup leaks bounds horizon scheduler history clear).state ≤
          2 * horizon + 1 := by
      have := (application setup leaks).trace_bound (initialLaw setup) horizon (NativeScheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
          (NativeScheduler)
          (nativeClearHistory setup leaks bounds horizon scheduler history clear).trace)
      omega
    exact near.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast depth) (by
      have := slotRetention_le_one (positive n).le (le_one n)
      positivity))

end Vegas.RecoveryOnePacket
