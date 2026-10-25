/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalComparisons
import Vegas.Game.SequentialPhaseCompletion
import Vegas.Game.SequentialPhaseLimit
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
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "MMenu" => menu setup leaks bounds
local notation "MP" => ReactiveApplication.ResponseMenu.protocol (MMenu) (initialLaw setup)
  horizon scheduler
local notation "Base" => phaseExclusionBase setup EventGraph.ExecutionMode.sequential
  (runtime setup) leaks

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

private local instance preservationNativeNature :
    (application setup (oldLeaks)).FiniteNature (Vegas.initialLaw setup) (NativeScheduler) :=
  nativeNature setup leaks scheduler

private local instance preservationNativeInformation (who : Player) : DecidableEq
    ((onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
      (NativeScheduler)).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

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
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (initialLaw setup) horizon
        scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon
        scheduler bound)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initialLaw setup) horizon
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
        ((MMenu).decisionInformationAntichain (initialLaw setup) horizon scheduler)
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
  let floors := fun n => combinedFloor setup (oldLeaks) bounds horizon (NativeScheduler)
    (sourceSequence n)
  let scale := fun n => trembleScale (floors n) (2 * horizon + 2) n
  have positive : ∀ n, 0 < scale n := fun n => trembleScale_pos
    (combinedFloor_pos setup (oldLeaks) bounds horizon (NativeScheduler) (sourceSequence n))
  have le_one : ∀ n, scale n ≤ 1 := fun n => trembleScale_le_one
    (combinedFloor_pos setup (oldLeaks) bounds horizon (NativeScheduler) (sourceSequence n)).le
    (combinedFloor_le_one setup (oldLeaks) bounds horizon (NativeScheduler) (sourceSequence n))
  have vanishes : Tendsto scale atTop (nhds 0) := tendsto_trembleScale _
    (fun n => combinedFloor_pos setup (oldLeaks) bounds horizon (NativeScheduler)
      (sourceSequence n))
    (fun n => combinedFloor_le_one setup (oldLeaks) bounds horizon (NativeScheduler)
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
  let range := fun who : Player => max 0 (max (excludedPayoff who) (upperUtility who)) -
    min 0 (min (excludedPayoff who) (lowerUtility who))
  let payoffBound : ℝ := ∑ who, range who
  have rangeNonnegative : ∀ who, 0 ≤ range who := by
    intro who
    exact sub_nonneg.mpr ((min_le_left 0 _).trans (le_max_left 0 _))
  have nonnegative : 0 ≤ payoffBound := Finset.sum_nonneg fun who _ => rangeNonnegative who
  have rangeLe : ∀ who, range who ≤ payoffBound := fun who =>
    Finset.single_le_sum (fun other _ => rangeNonnegative other) (Finset.mem_univ who)
  obtain ⟨readoutBounded, excludedBounded⟩ := exclusionPayoffs_bounded setup parameter utility
    excludedPayoff lowerUtility upperUtility lower_le le_upper
  have payoffBounded : ∀ who (final : (MP).History),
      |(Base (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
          final.state who| ≤ payoffBound := by
    intro who final
    have within := phaseExclusionBase_mem_Icc setup .sequential (runtime setup) leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
      lowerUtility upperUtility (fun terminal => lower_le (setup.parameterOutcome parameter
          terminal))
      (fun terminal => le_upper (setup.parameterOutcome parameter terminal)) final.state who
    have low := min_le_left 0 (min (excludedPayoff who) (lowerUtility who))
    have high := le_max_left 0 (max (excludedPayoff who) (upperUtility who))
    apply le_trans (b := range who) _ (rangeLe who)
    exact abs_le.mpr ⟨by dsimp only [range]; linarith [within.1],
      by dsimp only [range]; linarith [within.2]⟩
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
  obtain ⟨phaseSE, phaseLaw⟩ :=
    sequentialEquilibrium_of_local_comparisons setup leaks bounds horizon
      scheduler parameter utility excludedPayoff wellFormed covers capacity opportunity inclusion
      timely completes intended sourceSequence sourceConverges sourceRational scale positive
      le_one vanishes weights fallback sequence componentAssembled limit index increasing converges
      consistent freeOptimal error errorVanishes comparisons
  have noExclusion := initialized_limit_no_exclusion setup leaks bounds horizon scheduler
    opportunity inclusion timely completes wellFormed covers capacity sourceSequence scale positive
    le_one vanishes weights fallback sequence componentAssembled limit index increasing
    (fun who site => converges.strategy who site)
  exact ⟨limit, phaseSE, noExclusion, phaseLaw⟩

end Vegas.SequentialPhase
