/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseInitializedLaw
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit

/-! # Sequential phase equilibrium limits from the original completion witness -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [Finite setup.intendedProtocol.History]
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "Initial" => initialLaw setup
local notation "R" => model setup leaks bounds horizon scheduler
local notation "menu" => SequentialPhase.menu setup leaks bounds
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (SequentialPhase.menu setup leaks bounds) (Initial) horizon scheduler

attribute [local instance] phaseInfoDecidableEq

/-- Pure-choice comparisons complete the same actual phase witness. Its
original initialized joint typed readout and base-payoff law is preserved at that limit. -/
theorem sequentialEquilibrium_of_local_comparisons {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler
        bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (source : setup.intendedModel.BehavioralAssessment)
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
      source.truncatedContinuationContext site
        (fun final => (intendedReadoutExclusion setup parameter utility excludedPayoff final).2 who)
        (instructionCount setup.program + 1))
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0))
    (weights : ℕ → ∀ p, PMF
      (Part setup leaks bounds horizon scheduler bounds.candidateCount p))
    (fallback : ∀ who, (R).Policy who)
    (sequence : ℕ → (R).BehavioralAssessment)
    (assembled : ∀ n, (sequence n).strategy =
      componentStrategy setup leaks bounds horizon scheduler fallback (sourceSequence n) (scale n)
        (positive n).le (le_one n) (weights n))
    (limit : (R).BehavioralAssessment) (index : ℕ → ℕ) (increasing : StrictMono index)
    (converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit)
    (consistent : limit.IsSequentiallyConsistent
      ((menu).decisionRecall Initial horizon scheduler).decisionInformationAntichain)
    (freeOptimal : ∀ who (site : (R).InformationSite who),
      FreeAgent setup leaks bounds horizon scheduler ((R).agentAt site) →
      ∀ law : PMF ((R).Choice who site.1),
        (limit.continuationContext ((menu).bounded Initial horizon scheduler).wellFoundedHistories
          site (fun final => (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
                final.state
            who)).value ((limit.strategy who).withLaw site.1 law) ≤
        (limit.continuationContext ((menu).bounded Initial horizon scheduler).wellFoundedHistories
          site (fun final => (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
                final.state
            who)).value (limit.strategy who))
    (comparisonError : ℕ → ℝ) (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (comparisons : ∀ n who (site : (R).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((R).agentAt site) →
      ∀ choice : (R).Choice who site.1,
        localGain (2 * horizon + 1) (fun final => final.state)
            ((phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff))
                (sequence n) site
            (PMF.pure choice) ≤ comparisonError n ∨
          ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
            localGain (2 * horizon + 1) (fun final => final.state)
                ((phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff))
                (sequence n) site
                (PMF.pure choice) ≤
              expect mixture (fun deviation =>
                let compared := setup.intendedModel.assessmentComparisonWith
                  (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
                  (intendedReadoutExclusion setup parameter utility excludedPayoff)
                  (sourceSequence n) who deviation
                expect compared.alternative (fun outcome => outcome.2 who) -
                  expect compared.prescribed (fun outcome => outcome.2 who)) + comparisonError n) :
    limit.IsSequentialEquilibriumFor
        ((menu).decisionRecall Initial horizon scheduler).decisionInformationAntichain
        (fun who site => limit.truncatedContinuationContext site
          (fun final => (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
                final.state who)
          (2 * horizon + 1)) ∧
      ((R).runBehavioral limit.strategy (2 * horizon + 1)).map (fun final =>
        (phaseSourceReadout setup .sequential (runtime setup) leaks final.state,
          (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
                final.state)) =
        (setup.intendedModel.runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  let sourceObserve := intendedReadoutExclusion setup parameter utility excludedPayoff
  let targetObserve := fun final : (RP).History =>
    (phaseSourceReadout setup .sequential (runtime setup) leaks final.state,
      (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
                final.state)
  let payoff := fun outcome : Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
    fun who => outcome.2 who
  let budget : ℝ := (Fintype.card Player * (2 * horizon + 1) : ℕ)
  let lawError : ℕ → ℝ := fun n => 2 * (budget * (1 - slotRetention (scale n)))
  have lawVanishes : Tendsto lawError atTop (nhds 0) := by
    have retained := tendsto_slotRetention vanishes
    have negligible : Tendsto (fun n => budget * (1 - slotRetention (scale n))) atTop (nhds 0) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub retained).const_mul budget
    simpa only [mul_zero] using negligible.const_mul 2
  have initialized (n : ℕ) (outcome : Option (State L setup.program.terminalCtx) × (Player → ℝ)) :
      |((((R).runBehavioral (sequence n).strategy (2 * horizon + 1)).map targetObserve)
        outcome).toReal -
        (((setup.intendedModel.runBehavioral (sourceSequence n).strategy
          (instructionCount setup.program + 1)).map sourceObserve) outcome).toReal| ≤ lawError n :=
      by
    rw [assembled n]
    exact (component_initialized_readout_withinTV setup leaks bounds horizon scheduler opportunity
      inclusion timely completes wellFormed covers capacity sourceSequence scale positive le_one
      weights n fallback parameter utility excludedPayoff).apply outcome
  refine sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve targetObserve
    (instructionCount setup.program + 1) (2 * horizon + 1)
    ((menu).bounded Initial horizon scheduler) ((menu).decisionRecall Initial horizon scheduler)
    payoff source sourceSequence sourceConverges sourceRational sequence
    (fun _ site => ¬ FreeAgent setup leaks bounds horizon scheduler ((R).agentAt site))
    comparisonError errorVanishes (fun n who site notFree choice => ?_)
    lawError lawVanishes initialized limit index increasing converges consistent ?_
  · simpa only [localGain, assessmentComparisonWith, expect_map, targetObserve, sourceObserve,
      payoff, Function.comp_def] using comparisons n who site notFree choice
  · intro who site free law
    rw [← limit.continuationContext_eq_truncated_of_bounded
      ((menu).bounded Initial horizon scheduler).wellFoundedHistories
        ((menu).bounded Initial horizon scheduler)]
    exact freeOptimal who site (not_not.mp free) law

end Vegas.SequentialPhase
