/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalComparisons
import Vegas.Game.SequentialPhaseCompletion
import Vegas.Game.SequentialPhaseInitializedLaw
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit
import Vegas.Game.SequentialPhaseInitializedClearance
import Vegas.Game.OnePacketCertificateAssembly

/-! # Intended sequential equilibria in the canonical singleton phase game -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup)
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "MMenu" => menu setup leaks bounds
local notation "MP" => ReactiveApplication.ResponseMenu.protocol (MMenu) (phaseInitialLaw setup)
  horizon scheduler
local notation "Base" => phaseExclusionBase setup EventGraph.ExecutionMode.sequential
  (runtime setup) leaks

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- Every intended sequential equilibrium has a canonical singleton phase
equilibrium preserving the same joint typed readout and base-payoff law, with no
physical exclusions on its paths. -/
theorem intended_sequentialEquilibrium_preserved
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (phaseInitialLaw setup) horizon
        scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (phaseInitialLaw setup)
        horizon
        scheduler bound)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (phaseInitialLaw setup) horizon
        scheduler)
    (timely : AsyncTimely (runtime setup) delay bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount) :
    ∃ canonical : (M).BehavioralAssessment,
      canonical.IsSequentialEquilibriumFor
        ((MMenu).decisionInformationAntichain (phaseInitialLaw setup) horizon scheduler)
        (fun who site => canonical.truncatedContinuationContext site
          (fun final => (Base (fun terminal => utility (setup.parameterOutcome parameter
              terminal)) excludedPayoff) final.state who)
          (2 * horizon + 1)) ∧
      (∀ final ∈ ((M).runBehavioral canonical.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control → control.execution.application.current.excluded =
            ∅) ∧
      ((M).runBehavioral canonical.strategy (2 * horizon + 1)).map (fun final =>
        (phaseSourceReadout setup .sequential (runtime setup) leaks final.state, (Base (fun
            terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
            final.state)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  obtain ⟨sourceSequence, sourceMixed, sourceBayes, sourceConverges, sourceRational⟩ :=
    setup.intended_exclusionSource wellFormed parameter utility excludedPayoff intended
      equilibrium
  let floors := fun n => combinedFloor setup (RecoveryLeaks) bounds horizon (NativeScheduler)
    (sourceSequence n)
  let scale := fun n => trembleScale (floors n) (2 * horizon + 2) n
  have positive : ∀ n, 0 < scale n := fun n => trembleScale_pos
    (combinedFloor_pos setup (RecoveryLeaks) bounds horizon (NativeScheduler) (sourceSequence n))
  have le_one : ∀ n, scale n ≤ 1 := fun n => trembleScale_le_one
    (combinedFloor_pos setup (RecoveryLeaks) bounds horizon (NativeScheduler) (sourceSequence n)).le
    (combinedFloor_le_one setup (RecoveryLeaks) bounds horizon (NativeScheduler) (sourceSequence n))
  have vanishes : Tendsto scale atTop (nhds 0) := tendsto_trembleScale _
    (fun n => combinedFloor_pos setup (RecoveryLeaks) bounds horizon (NativeScheduler)
      (sourceSequence n))
    (fun n => combinedFloor_le_one setup (RecoveryLeaks) bounds horizon (NativeScheduler)
      (sourceSequence n))
  obtain ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
      consistent, pooled, _limits, freeOptimal⟩ :=
    exists_consistent_completion setup leaks bounds horizon scheduler parameter utility
        excludedPayoff
      sourceSequence bounds.candidateCount scale positive le_one vanishes
  let fallback : ∀ who, (M).Policy who := fun _ _ => Classical.arbitrary _
  have componentAssembled : ∀ n, (sequence n).strategy = componentStrategy setup leaks bounds
      horizon scheduler fallback (sourceSequence n) (scale n) (positive n).le (le_one n)
      (weights n) := assembled
  let payoffBound : ℝ := ∑ player,
    (max 0 (max (excludedPayoff player) (upperUtility player)) -
      min 0 (min (excludedPayoff player) (lowerUtility player)))
  obtain ⟨nonnegative, readoutBounded, excludedBounded⟩ :=
    exclusionPayoffs_bounded setup parameter utility excludedPayoff lowerUtility upperUtility
      lower_le le_upper
  have payoffBounded : ∀ who (final : (MP).History),
      |Base (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
        final.state who| ≤ payoffBound := by
    intro who final
    exact GameTheory.Math.abs_le_sum_interval_width
      (fun player => min 0 (min (excludedPayoff player) (lowerUtility player)))
      (fun player => max 0 (max (excludedPayoff player) (upperUtility player)))
      (fun _ => min_le_left _ _) (fun _ => le_max_left _ _) who
      (phaseExclusionBase_mem_Icc setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
        lowerUtility upperUtility (fun terminal => lower_le (setup.parameterOutcome parameter
          terminal)) (fun terminal => le_upper (setup.parameterOutcome parameter terminal))
        final.state who)
  obtain ⟨error, errorVanishes, comparisons⟩ :
      ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
        ∀ n who (site : (M).InformationSite who),
          ¬ FreeAgent setup leaks bounds horizon scheduler
            ((M).agentAt site) →
          ∀ choice : (M).Choice who site.1,
            localGain (2 * horizon + 1) (fun final => final.state)
                ((Base (fun terminal => utility (setup.parameterOutcome parameter terminal))
                    excludedPayoff)) (sequence n) site
                (PMF.pure choice) ≤ error n ∨
              ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
                localGain (2 * horizon + 1) (fun final => final.state)
                    ((Base (fun terminal => utility (setup.parameterOutcome parameter terminal))
                        excludedPayoff)) (sequence n) site
                    (PMF.pure choice) ≤
                  expect mixture (intendedSiteGain setup parameter utility excludedPayoff
                    (sourceSequence n)) + error n := by
    by_cases slots_pos : 0 < bounds.candidateCount
    · exact local_comparisons setup leaks bounds horizon scheduler wellFormed independent observable
        sourceSequence sourceMixed sourceBayes scale positive le_one (fun _ => rfl) covers
            coversInputs
        capacity slots_pos weights sequence (fun _ => fallback) componentAssembled mixed bayes
        opportunity inclusion timely parameter utility excludedPayoff payoffBound nonnegative
            completes
        payoffBounded excludedBounded below upperUtility le_upper readoutBounded pooled
    · refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
      intro _ who _ _ _
      have impossible := capacity who
      omega
  let sourceObserve := intendedReadoutExclusion setup parameter utility excludedPayoff
  let targetObserve := fun final : (MP).History =>
    (phaseSourceReadout setup .sequential (runtime setup) leaks final.state,
      (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
                final.state)
  let payoff := fun outcome : Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
    fun who => outcome.2 who
  let budget : ℝ := (min (Fintype.card Player) 1 * horizon : ℕ)
  let lawError : ℕ → ℝ := fun n => 2 * (budget * (1 - slotRetention (scale n)))
  have lawVanishes : Tendsto lawError atTop (nhds 0) := by
    have retained := tendsto_slotRetention vanishes
    have negligible : Tendsto (fun n => budget * (1 - slotRetention (scale n))) atTop (nhds 0) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub retained).const_mul budget
    simpa only [mul_zero] using negligible.const_mul 2
  have initialized (n : ℕ) (outcome : Option (State L setup.program.terminalCtx) × (Player → ℝ)) :
      |((((M).runBehavioral (sequence n).strategy (2 * horizon + 1)).map targetObserve)
        outcome).toReal -
        (((setup.intendedModel.runBehavioral (sourceSequence n).strategy
          (instructionCount setup.program + 1)).map sourceObserve) outcome).toReal| ≤ lawError n :=
      by
    rw [componentAssembled n]
    exact (component_initialized_readout_withinTV setup leaks bounds horizon scheduler opportunity
      inclusion timely completes wellFormed covers capacity sourceSequence scale positive le_one
      weights n fallback parameter utility excludedPayoff).apply outcome
  obtain ⟨phaseSE, phaseLaw⟩ :=
    sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve targetObserve
      (instructionCount setup.program + 1) (2 * horizon + 1)
      ((MMenu).bounded (phaseInitialLaw setup) horizon scheduler)
      ((MMenu).decisionRecall (phaseInitialLaw setup) horizon scheduler) payoff intended
          sourceSequence
      sourceConverges sourceRational sequence
      (fun _ site => ¬ FreeAgent setup leaks bounds horizon scheduler ((M).agentAt site))
      error errorVanishes (fun n who site notFree choice => by
        have compared := comparisons n who site notFree choice
        unfold intendedSiteGain payoffComponent at compared
        simpa only [localGain, assessmentComparisonWith, expect_map, targetObserve, sourceObserve,
          payoff, Function.comp_def] using compared)
      lawError lawVanishes initialized limit index increasing converges consistent
      (fun who site free law => by
        rw [← limit.continuationContext_eq_truncated_of_bounded
          ((MMenu).bounded (phaseInitialLaw setup) horizon scheduler).wellFoundedHistories
          ((MMenu).bounded (phaseInitialLaw setup) horizon scheduler)]
        exact freeOptimal who site (not_not.mp free) law)
  have noExclusion := initialized_limit_no_exclusion setup leaks bounds horizon scheduler
    opportunity inclusion timely completes wellFormed covers capacity sourceSequence scale positive
    le_one vanishes weights fallback sequence componentAssembled limit index increasing
    (fun who site => converges.strategy who site)
  exact ⟨limit, phaseSE, noExclusion, phaseLaw⟩

end Vegas.SequentialPhase
