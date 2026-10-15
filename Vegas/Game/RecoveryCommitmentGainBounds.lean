/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitmentBeliefValue
import Vegas.Game.RecoverySourceBeliefBounds
import Vegas.Game.RecoveryIrregularBeliefBounds
import Vegas.Game.RecoveryFirstActivationValue
import Vegas.Game.RecoveryCompletionPotential
import Vegas.Game.IntendedChoiceReach
import Vegas.Game.OnePacketNonLateValueBlind

/-! # Uniform source incentive bounds for nonlate commitments -/

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
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

open Classical in
/-- The same common weights give a uniformly vanishing incentive error for
every intended nonlate commitment, against an original source deviation. -/
theorem nativeComparison_intendedCommitment_gain_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who) (choice : (N).Choice who site.1),
        ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ LateDelivery setup leaks who site.1 →
        CommitsAtTurn setup leaks bounds horizon (NativeScheduler) who site choice →
        IntendedCommitment setup leaks bounds horizon (NativeScheduler) site choice →
        ∃ sourceDeviation : setup.intendedModel.AssessmentDeviation who,
          let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
            positive le_one weights n
          let certificate := ((Menu).bounded (initialLaw setup) horizon
            (NativeScheduler)).wellFoundedHistories
          let stopped := fun final : (NP).History => ¬ Clear final.state ∨
            DecodedState setup leaks (failureProfile setup.program)
              (ProtocolState.OwesFailure who setup.program) final.state
          let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
            exclusionBase setup parameter utility excludedPayoff leaks final.state who
          expect ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
            positive le_one weights n).belief who site) (fun history =>
              expect ((N).runBehavioralUntil certificate
                  (Profile.update (sig := (N).behavioralSignature) common who
                    ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
                expect ((N).runBehavioralUntil certificate common stopped history.1) payoff) ≤
            intendedSiteGain setup parameter utility excludedPayoff (sequence n) sourceDeviation +
              error n := by
  obtain ⟨distance, distanceLimit, posterior⟩ := nativeComparison_source_belief_bounds setup leaks
    bounds horizon scheduler wellFormed independent sequence sourceMixed sourceBayes scale positive
    le_one scaleEq covers coversInputs capacity weights
  obtain ⟨drift, driftLimit, irregular⟩ := nativeComparison_irregular_bounds setup leaks bounds
    horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one scaleEq
    covers coversInputs capacity weights
  let retentionError := fun n => 1 - slotRetention (scale n)
  let error := fun n =>
    (2 * ((2 * payoffBound * (Fintype.card Player * retentionError n))) *
      (2 * horizon + 1) + 2 * payoffBound * retentionError n) +
    4 * payoffBound * drift n + 2 * payoffBound * distance n
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    have identity : scale = fun n => trembleScale
        (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
        (2 * horizon + 2) n := funext scaleEq
    rw [identity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup leaks bounds horizon (NativeScheduler) (sequence n))
      (fun n => combinedFloor_le_one setup leaks bounds horizon (NativeScheduler) (sequence n))
  have retentionLimit : Tendsto retentionError atTop (nhds 0) := by
    simpa only [retentionError, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_slotRetention scaleLimit)
  have errorLimit : Tendsto error atTop (nhds 0) := by
    have first := ((retentionLimit.const_mul (Fintype.card Player : ℝ)).const_mul
      (2 * payoffBound)).const_mul 2
    have limit := ((first.mul_const (2 * horizon + 1 : ℝ)).add
      (retentionLimit.const_mul (2 * payoffBound))).add
      (driftLimit.const_mul (4 * payoffBound))
    simpa only [zero_mul, mul_zero, zero_add, add_zero] using
      limit.add (distanceLimit.const_mul (2 * payoffBound))
  refine ⟨error, errorLimit, ?_⟩
  intro n who site choice notFree notOwing nonlate atTurn intendedChoice
  obtain ⟨past, view, response, event, atSite, selected, submitted, turn⟩ := atTurn
  have forced := forcedAgent_of_not_free setup leaks bounds horizon (NativeScheduler) notFree
  have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler) notOwing
  have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
  obtain ⟨sourceChoice, averaged⟩ :=
    nativeComparison_intendedCommitment_belief_comparison setup leaks bounds horizon scheduler
      wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion
      timely completes site choice notFree notOwing nonlate
      ⟨past, view, response, event, atSite, selected, submitted, turn⟩ intendedChoice atSite
      decision
      parameter utility excludedPayoff below (upper who) (fun outcome => le_upper outcome who)
      boundNonneg (readoutBounded who) (excludedBounded who)
  let sourceSite := projectedSite setup leaks decision
  let deviation : setup.intendedModel.AssessmentDeviation who :=
    (sourceSite, ((sequence n).strategy who).commit sourceSite.1 sourceChoice)
  refine ⟨deviation, ?_⟩
  intro common certificate stopped payoff
  let sourceGain := setup.intendedModel.historyGain
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
    (sequence n) deviation
  have sourceBounded : ∀ history, |sourceGain history| ≤ 2 * payoffBound :=
    intended_historyGain_abs_le_of_readoutBounded (sequence n) parameter utility excludedPayoff
      boundNonneg (readoutBounded who) deviation
  have transported := expect_sub_le_of_bounded
    (((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
      le_one weights n).belief who site).map
        (replayProjection setup leaks bounds horizon (NativeScheduler) sourceSite site atSite rfl))
    ((sequence n).belief who sourceSite) sourceGain sourceBounded
  have near := posterior n who site notFree notOwing atSite turn decision
  have rare := irregular n who site notFree notOwing atSite turn
  have sourceEq := setup.intendedModel.gain_eq_expect_historyGain
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
    (sequence n) deviation
  have scaled := mul_le_mul_of_nonneg_left near (by positivity : 0 ≤ 2 * payoffBound)
  have scaledRare := mul_le_mul_of_nonneg_left rare (by positivity : 0 ≤ 4 * payoffBound)
  dsimp only at averaged
  let nativeGain := expect
    ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
      le_one weights n).belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff)
  let replayedMean := expect
    (((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
      le_one weights n).belief who site).map
        (replayProjection setup leaks bounds horizon (NativeScheduler) sourceSite site atSite rfl))
    sourceGain
  let sourceMean := expect ((sequence n).belief who sourceSite) sourceGain
  let irregularMass := expect
    ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
      le_one weights n).belief who site) (fun history =>
        if RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who
          history.1.trace then (0 : ℝ) else 1)
  have compared : nativeGain ≤ replayedMean +
      (2 * ((2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n))) +
      4 * payoffBound * irregularMass := averaged
  have transferred : replayedMean - sourceMean ≤ 2 * payoffBound * distance n :=
    transported.trans scaled
  have rareBound : 4 * payoffBound * irregularMass ≤ 4 * payoffBound * drift n := scaledRare
  change intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation =
    sourceMean at sourceEq
  change nativeGain ≤ intendedSiteGain setup parameter utility excludedPayoff (sequence n)
    deviation + error n
  rw [sourceEq]
  dsimp only [error, retentionError]
  linarith only [compared, transferred, rareBound]

end Vegas.RecoveryOnePacket
