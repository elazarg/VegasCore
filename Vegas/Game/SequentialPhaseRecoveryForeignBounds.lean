/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseRecoveryForeignExit
import Vegas.Game.RecoveryIrregularBeliefBounds

/-! # Uniform foreign-exit error for the actual phase-derived recovery comparison -/

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

local instance posteriorComparisonHistory : Fintype ((RMenu).protocol
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).History :=
  sourceHistoryFintype setup leaks bounds horizon scheduler

local instance posteriorComparisonInformation (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds
      ((Vegas.initialLaw setup).map (fun native =>
        (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).InfoState who) :=
  sourceInfoDecidableEq setup leaks bounds horizon scheduler who

local instance posteriorComparisonNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance posteriorNativeInformation (who : Player) : DecidableEq ((N).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

local instance posteriorRecoveryNature :
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) (oldScheduler) :=
  recoveryNature setup leaks scheduler

local instance posteriorNativeHistory : Fintype (NP).History :=
  @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (NMenu) (Vegas.initialLaw setup)
    horizon (NativeScheduler) inferInstance (nativeNature setup leaks scheduler)

variable {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- Physical phase opportunity and inclusion give uniformly vanishing foreign
native debt-stopped mass at actual forced debt-free recovery comparison sites.
Past irregularity and future exceptional choices are both retained in the error. -/
theorem recovery_comparison_foreign_exit_bounds [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (initialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (initialLaw setup)
      horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate : (NP).WellFoundedHistories) (rawCertificate : (RawNative).WellFoundedHistories) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds Initial horizon (oldScheduler)
          ((R).agentAt site) →
        ¬ RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds Initial horizon (oldScheduler)
          ((R).agentAt site) →
        ∀ {past : List (recoveryApplication (runtime setup) (oldLeaks)).PlayerEntry}
          {view : (recoveryApplication (runtime setup) (oldLeaks)).PlayerView},
        site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        ∀ alternative : (R).BehavioralPolicy who,
        (((((recoveryComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
          le_one weights n).belief who site).map Subtype.val).bind
          (RecoveryOnePacket.nativeDebtStoppedLaw setup (oldLeaks) bounds horizon (oldScheduler)
            rawCertificate (Profile.update (sig := (R).behavioralSignature)
              (recoveryComparisonStrategy setup leaks bounds horizon scheduler (sequence n)
                (scale n) (positive n).le (le_one n) (weights n)) who alternative)
            who)).toOuterMeasure {label | ForeignExclusionLabel who label}).toReal ≤ error n := by
  classical
  let assessments := recoveryComparisonSequence setup leaks bounds horizon scheduler sequence scale
    positive le_one weights
  let oldWeights := fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler
    (weights n)
  let fallback := fun _ : ℕ => recoveryComparisonFallback setup leaks bounds horizon scheduler
  have assembled (n) : (assessments n).strategy =
      (R).agentBehavior (R).playedInformation (fallback n) (fun agent =>
        (oldWeights n (RecoveryOnePacket.pool setup (oldLeaks) bounds Initial horizon
          (oldScheduler) agent)).bind
          (RecoveryOnePacket.component setup (oldLeaks) bounds Initial horizon (oldScheduler)
            (sequence n) (scale n) (positive n).le (le_one n) agent)) := rfl
  have bayes (n) := recoveryComparisonSequence_bayes setup leaks bounds horizon scheduler sequence
    scale positive le_one weights n
  obtain ⟨drift, driftLimit, irregular⟩ := RecoveryOnePacket.recovery_irregular_belief_bounds setup
    (oldLeaks) bounds horizon (oldScheduler) wellFormed independent observable sequence sourceMixed
    scale positive le_one scaleEq covers coversInputs capacity oldWeights assessments fallback
    assembled bayes
  have scaleIdentity : scale = (fun n => trembleScale
      (combinedFloor setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n))
        (2 * horizon + 2) n) := funext scaleEq
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    rw [scaleIdentity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n))
      (fun n => combinedFloor_le_one setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n))
  have deltaLimit : Tendsto (fun n => (scale n) ^ 2 + scale n) atTop (nhds 0) := by
    simpa using (scaleLimit.pow 2).add scaleLimit
  let error := fun n => drift n + ((scale n) ^ 2 + scale n) * (2 * horizon + 1)
  refine ⟨error, ?_, ?_⟩
  · simpa only [error, zero_mul, add_zero] using
      driftLimit.add (deltaLimit.mul_const (2 * (horizon : ℝ) + 1))
  intro n who site notFree notOwing past view atSite event turn alternative
  obtain ⟨nativeSite, project, _nativeInput, projection, states, _law, irregularMass⟩ :=
    irregular n who site notFree notOwing atSite turn
  let posterior := (assessments n).belief who site
  let updated := Profile.update (sig := (R).behavioralSignature) (assessments n).strategy who
    alternative
  let kernel := RecoveryOnePacket.nativeDebtStoppedLaw setup (oldLeaks) bounds horizon
    (oldScheduler) rawCertificate updated who
  let exits := {label : Finset Player ⊕ (RawNative).History | ForeignExclusionLabel who label}
  let indicator := fun label => @ite ℝ (label ∈ exits) (Classical.propDecidable _) 1 0
  let forget := fun history : (R).InformationHistory who site.1 => (project history).1
  let bad := {history :
      ((NMenu).protocol (Vegas.initialLaw setup) horizon (NativeScheduler)).History |
    ¬ RegularTrace setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n) who history.trace}
  let badIndicator := fun history => @ite ℝ (history ∈ bad) (Classical.propDecidable _) 1 0
  let badPayoff := badIndicator ∘ forget
  let future := fun history : (R).InformationHistory who site.1 =>
    expect (kernel history.1) indicator
  let cost := ((scale n) ^ 2 + scale n) * (2 * horizon + 1)
  let clear := fun history : (R).InformationHistory who site.1 => (projection history).choose
  have indicatorBounded : ∀ label, |indicator label| ≤ 1 := by
    intro label
    dsimp only [indicator]
    split <;> norm_num
  have futureBounded : ∀ history, |future history| ≤ 1 :=
    fun _ => expect_abs_le_of_bounded (by norm_num) indicatorBounded
  have costNonnegative : 0 ≤ cost :=
    mul_nonneg (add_nonneg (sq_nonneg _) (positive n).le) (by positivity)
  have pointwise : ∀ history ∈ posterior.support,
      future history ≤ badPayoff history + cost := by
    intro history _member
    by_cases regular : RegularTrace setup (oldLeaks) bounds horizon (NativeScheduler)
        (sequence n) who
        (project history).1.trace
    · have same := RecoveryOnePacket.nativeClearHistory_eq_of_raw setup (oldLeaks) bounds horizon
        (oldScheduler) history.1
        (clear history) (project history).1 (projection history).choose_spec
      have nativeRegular : RegularTrace setup (oldLeaks) bounds horizon (NativeScheduler)
          (sequence n)
          who (RecoveryOnePacket.nativeClearHistory setup (oldLeaks) bounds horizon (oldScheduler)
            history.1 (clear history)).trace :=
        Eq.mp (congrArg (fun prior :
          (onePacketProtocol setup (oldLeaks) bounds horizon (NativeScheduler)).History =>
            RegularTrace setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n) who
              prior.trace)
          same.symm) regular
      let normalized : (R).InformationHistory who (some (past, view)) :=
        ⟨history.1, history.2.trans atSite⟩
      obtain ⟨control, state, currentTurn⟩ :=
        RecoveryOnePacket.informationHistory_control_turn setup (oldLeaks) bounds horizon
        (oldScheduler) normalized turn
      have row := recovery_nativeDebtStopped_foreign_mass_le_rank setup leaks bounds horizon
        scheduler wellFormed covers capacity sequence scale positive le_one weights n who
        alternative opportunity inclusion timely certificate rawCertificate history.1
        (clear history)
        control state event currentTurn nativeRegular
      have depth := (application setup (oldLeaks)).trace_bound (Vegas.initialLaw setup) horizon
        (NativeScheduler) ((NMenu).toRawTrace (Vegas.initialLaw setup) horizon (NativeScheduler)
          (project history).1.trace)
      have rankBound : (application setup (oldLeaks)).rank horizon
          (protocolState (runtime setup) (oldLeaks) history.1.state) ≤ 2 * horizon + 1 := by
        rw [← states history]
        omega
      have rankReal : ((application setup (oldLeaks)).rank horizon
          (protocolState (runtime setup) (oldLeaks) history.1.state) : ℝ) ≤ 2 * horizon + 1 := by
        exact_mod_cast rankBound
      have value : future history ≤ cost := by
        calc
          future history = ((kernel history.1).toOuterMeasure exits).toReal :=
            expect_indicator (kernel history.1) exits
          _ ≤ ((scale n) ^ 2 + scale n) * (application setup (oldLeaks)).rank horizon
              (protocolState (runtime setup) (oldLeaks) history.1.state) := row
          _ ≤ cost := mul_le_mul_of_nonneg_left rankReal
            (add_nonneg (sq_nonneg _) (positive n).le)
      have badFalse : badPayoff history = 0 := by
        simp [badPayoff, badIndicator, bad, forget, regular]
      simpa only [badFalse, zero_add] using value
    · have badTrue : badPayoff history = 1 := by
        simp [badPayoff, badIndicator, bad, forget, regular]
      have upper : future history ≤ 1 + cost :=
        (le_abs_self _).trans
          ((futureBounded history).trans (le_add_of_nonneg_right costNonnegative))
      simpa only [badTrue] using upper
  have badExpectation : expect posterior badPayoff ≤ drift n := by
    have equal : expect posterior badPayoff =
        ((posterior.map forget).toOuterMeasure bad).toReal :=
      (expect_map forget posterior badIndicator).symm.trans
        (expect_indicator (posterior.map forget) bad)
    exact equal.trans_le irregularMass
  have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  calc
    _ = expect ((posterior.map Subtype.val).bind kernel) indicator :=
      (expect_indicator ((posterior.map Subtype.val).bind kernel) exits).symm
    _ = expect (posterior.map Subtype.val) (fun history => expect (kernel history) indicator) :=
      expect_bind_tower_bounded (posterior.map Subtype.val) kernel indicator indicatorBounded
    _ = expect posterior future := expect_map Subtype.val posterior _
    _ ≤ expect posterior (fun history => badPayoff history + cost) := averaged
    _ = expect posterior badPayoff + cost :=
      (expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).trans
        (congrArg (fun value => expect posterior badPayoff + value)
          (expect_constant posterior cost))
    _ ≤ drift n + cost := add_le_add badExpectation (le_refl cost)
    _ = error n := rfl

end Vegas.SequentialPhase
