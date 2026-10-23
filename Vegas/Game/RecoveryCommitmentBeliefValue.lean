/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitmentComparisons

/-! # A single source deviation for all histories of a nonlate commitment -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

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
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

open Classical in
/-- A single source commitment bounds the average native gain; only irregular
histories contribute an additional bounded error. -/
theorem nativeComparison_intendedCommitment_belief_comparison [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notFree : ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site))
    (notOwing : ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site))
    (nonlate : ¬ LateDelivery setup leaks who site.1)
    (atTurn : CommitsAtTurn setup leaks bounds horizon (NativeScheduler) who site choice)
    (intendedChoice : IntendedCommitment setup leaks bounds horizon (NativeScheduler) site choice)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    :
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    let belief := (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n).belief who site
    ∃ sourceChoice : setup.intendedModel.Choice who (projectView setup leaks who site.1),
      expect belief (fun history =>
        expect ((N).runBehavioralUntil certificate
            (Profile.update (sig := (N).behavioralSignature) common who
              ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
          expect ((N).runBehavioralUntil certificate common stopped history.1) payoff) ≤
        expect (belief.map (replayProjection setup leaks bounds horizon (NativeScheduler)
            (projectedSite setup leaks decision) site atSite rfl))
          (setup.intendedModel.historyGain
            (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
            (intendedReadoutExclusion setup parameter utility excludedPayoff)
            (payoffComponent setup)
            (sequence n) (projectedSite setup leaks decision,
              ((sequence n).strategy who).commit
                (projectView setup leaks who site.1) sourceChoice)) +
        (2 * ((2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
          (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n))) +
        4 * payoffBound * expect belief (fun history =>
          if RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who
            history.1.trace then (0 : ℝ) else 1) := by
  intro common certificate stopped payoff belief
  obtain ⟨sourceChoice, perHistory⟩ :=
    nativeComparison_intendedCommitment_history_comparisons setup leaks bounds horizon scheduler
      wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion
      timely completes site choice notFree notOwing nonlate atTurn intendedChoice atSite decision
      parameter utility excludedPayoff below upper le_upper boundNonneg readoutBounded
      excludedBounded
  refine ⟨sourceChoice, ?_⟩
  let source := setup.intendedModel.historyGain
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
    (sequence n) (projectedSite setup leaks decision,
      ((sequence n).strategy who).commit (projectView setup leaks who site.1) sourceChoice)
  let replay := replayProjection setup leaks bounds horizon (NativeScheduler)
    (projectedSite setup leaks decision) site atSite rfl
  let native := fun history : (N).InformationHistory who site.1 =>
    expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff
  let error := 2 * ((2 * payoffBound *
      (Fintype.card Player * (1 - slotRetention (scale n)))) * (2 * horizon + 1)) +
    2 * payoffBound * (1 - slotRetention (scale n))
  let irregular := fun history : (N).InformationHistory who site.1 =>
    if RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who
      history.1.trace then (0 : ℝ) else 1
  have errorNonneg : 0 ≤ error := by
    have retention := slotRetention_le_one (positive n).le (le_one n)
    dsimp only [error]
    positivity
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · rw [exclusionBase_eq_readout]
      exact readoutBounded _
  have nativeBounded : ∀ history, |native history| ≤ 2 * payoffBound := by
    intro history
    have first := expect_abs_le_of_bounded (μ := (N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1)
      boundNonneg payoffBounded
    have second := expect_abs_le_of_bounded
      (μ := (N).runBehavioralUntil certificate common stopped history.1)
      boundNonneg payoffBounded
    dsimp only [native]
    exact (abs_sub _ _).trans (by linarith)
  have sourceBounded : ∀ history, |source history| ≤ 2 * payoffBound := by
    intro history
    have each : ∀ final : setup.intendedProtocol.History,
        |payoffComponent setup
          (intendedReadoutExclusion setup parameter utility excludedPayoff final) who| ≤
          payoffBound := fun _ => readoutBounded _
    dsimp only [source]
    unfold InformationModel.historyGain
    rw [expect_map, expect_map]
    simp only [Function.comp_def]
    have first := expect_abs_le_of_bounded (μ := setup.intendedModel.truncatedRunner
      (instructionCount setup.program + 1) (Profile.update
        (sig := setup.intendedModel.behavioralSignature) (sequence n).strategy who
        (((sequence n).strategy who).commit (projectView setup leaks who site.1) sourceChoice))
      history.1) boundNonneg each
    have second := expect_abs_le_of_bounded (μ := setup.intendedModel.truncatedRunner
      (instructionCount setup.program + 1) (Profile.update
        (sig := setup.intendedModel.behavioralSignature) (sequence n).strategy who
        ((sequence n).strategy who)) history.1) boundNonneg each
    exact (abs_sub _ _).trans (by linarith)
  have pointwise : ∀ history, native history ≤
      (source (replay history) + error) + 4 * payoffBound * irregular history := by
    intro history
    by_cases regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who
        history.1.trace
    · simp only [irregular, regular, ↓reduceIte, mul_zero, add_zero]
      simpa only [native, source, replay, error, add_assoc] using perHistory history regular
    · simp only [irregular, regular, ↓reduceIte, mul_one]
      linarith [(abs_le.mp (nativeBounded history)).2,
        (abs_le.mp (sourceBounded (replay history))).1]
  rw [expect_map]
  calc expect belief native ≤ expect belief
        (fun history => (source (replay history) + error) +
          4 * payoffBound * irregular history) :=
      expect_mono (fun history _ => pointwise history) (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _)
    _ = _ := by
      rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
        expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
        expect_constant, expect_const_mul]
      rfl

end Vegas.RecoveryOnePacket
