/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.SequentialOneShot
import GameTheoryExtensions.Protocol.ContinuationHorizon
import GameTheoryExtensions.Analysis.Protocol.UniformPolicyLimit
import GameTheoryExtensions.Protocol.ContinuationSimulation
import GameTheoryExtensions.Math.Probability.Support

/-! # Sequential equilibrium from local continuation comparisons

Only local target deviations need a simulation, up to a uniformly vanishing
gain error. A local choice can instead have gain bounded by that same error.
This includes private response aliases at implementation-only decision sites.

All comparisons use the original source assessment sequence. Intermediate
behavioral realizations need neither be equilibria nor converge at unreachable
information sets. One common target subsequence supplies consistent beliefs;
decision recall then upgrades limiting local optimality to whole-policy SE.
-/

noncomputable section

namespace GameTheory.ContinuationSimulation

open Protocol Protocol.InformationModel Protocol.ExecutionProtocol Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite E.History] [Finite T.History]
  [∀ who, DecidableEq (N.InfoState who)]
  [∀ who (site : N.InformationSite who), Fintype (N.InformationHistory who site.1)]

/-- Local target gains bounded by original-source gain mixtures, up to one
uniformly vanishing error, preserve sequential rationality at a common consistent
assessment limit. Mixtures may depend on the perturbation, site, and local lottery;
the source and target games and utilities remain fixed. An error-bound-only
branch covers harmless implementation choices with no source decision site.

The bounded target horizon covers completion. The source conclusion is its law
at the stated source fuel; choosing an adequate source horizon makes this a
terminal-law theorem. -/
theorem sequentialEquilibrium_of_local_comparisons_limit
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (targetClock : ∀ who (site : N.InformationSite who),
      ∃ depth, InformationSite.CommonDepth N site depth)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceMixed : (sourceSequence 0).IsFullyMixed)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalWithin
      (fun who history => utility (sourceObserve history) who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (comparisonError : ℕ → ℝ)
    (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (localComparisons : ∀ n who (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)),
      let comparison := N.assessmentComparison targetObserve targetFuel (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := M.assessmentComparison sourceObserve sourceFuel
                (sourceSequence n) who deviation
              expect sourceComparison.alternative (utility · who) -
                expect sourceComparison.prescribed (utility · who)) + comparisonError n)
    (initialized : ∀ n,
      (N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve =
        (M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve)
    (target : N.BehavioralAssessment) (index : ℕ → ℕ) (increasing : StrictMono index)
    (targetConverges : BehavioralAssessmentConvergesPointwise
      (fun n => targetSequence (index n)) target)
    (consistent : target.IsSequentiallyConsistent targetRecall.decisionInformationAntichain) :
    target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.continuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve := by
  classical
  have localOptimal (who : Player) (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)) :
      (target.continuationContext site
          (fun history => utility (targetObserve history) who) targetFuel).value
            ((target.strategy who).withLaw site.1 law) ≤
        (target.continuationContext site
          (fun history => utility (targetObserve history) who) targetFuel).value
            (target.strategy who) := by
    obtain ⟨error, nonnegative, vanishes, bound⟩ :=
      sourceConverges.exists_uniform_policy_gain_bound (sourceSequence 0) sourceMixed
        who (fun history => utility (sourceObserve history) who) sourceFuel (sourceRational who)
    have sourceBound (n : ℕ) (deviation : M.AssessmentDeviation who) :
        expect ((M.assessmentComparison sourceObserve sourceFuel (sourceSequence n)
          who deviation).alternative) (utility · who) -
          expect ((M.assessmentComparison sourceObserve sourceFuel (sourceSequence n)
            who deviation).prescribed) (utility · who) ≤ error n := by
      simpa only [assessmentComparison, expect_map, Context.value,
        BehavioralAssessment.continuationContext] using bound n deviation.1 deviation.2
    have targetBound (n : ℕ) :
        ((targetSequence n).continuationContext site
            (fun history => utility (targetObserve history) who) targetFuel).value
              (((targetSequence n).strategy who).withLaw site.1 law) -
          ((targetSequence n).continuationContext site
            (fun history => utility (targetObserve history) who) targetFuel).value
              ((targetSequence n).strategy who) ≤ error n + comparisonError n := by
      have comparison :
          expect ((N.assessmentComparison targetObserve targetFuel (targetSequence n) who
              (site, ((targetSequence n).strategy who).withLaw site.1 law)).alternative)
                (utility · who) -
            expect ((N.assessmentComparison targetObserve targetFuel (targetSequence n) who
              (site, ((targetSequence n).strategy who).withLaw site.1 law)).prescribed)
                (utility · who) ≤ error n + comparisonError n := by
        rcases localComparisons n who site law with harmless | ⟨mixture, comparison⟩
        · exact harmless.trans (le_add_of_nonneg_left (nonnegative n))
        · apply comparison.trans
          have estimate := FinDist.expect_mono (μ := mixture)
            (fun deviation _ => sourceBound n deviation)
          rw [expect_constant] at estimate
          dsimp only
          linarith
      simpa only [assessmentComparison, expect_map, Context.value,
        BehavioralAssessment.continuationContext] using comparison
    have alternate := targetConverges.context_value (targetSequence (index 0))
      (targetMixed (index 0)) site (fun history => utility (targetObserve history) who)
      targetFuel (fun n => ((targetSequence (index n)).strategy who).withLaw site.1 law)
      ((target.strategy who).withLaw site.1 law) (by
        intro decision
        by_cases same : decision = site
        · subst decision
          simpa only [BehavioralPolicy.withLaw_self] using pmfConvergesPointwise_const law
        · have different : decision.1 ≠ site.1 := fun equal => same (Subtype.ext equal)
          simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
            targetConverges.strategy who decision)
    have prescribed := targetConverges.context_value (targetSequence (index 0))
      (targetMixed (index 0)) site (fun history => utility (targetObserve history) who)
        targetFuel (fun n => (targetSequence (index n)).strategy who) (target.strategy who)
          (targetConverges.strategy who)
    exact sub_nonpos.mp (le_of_tendsto_of_tendsto (alternate.sub prescribed)
      (by simpa only [zero_add, Function.comp_def] using
        (vanishes.add errorVanishes).comp increasing.tendsto_atTop)
      (Eventually.of_forall fun n => targetBound (index n)))
  refine ⟨⟨?_, consistent⟩, ?_⟩
  · intro who site
    obtain ⟨depth, common⟩ := targetClock who site
    have within : depth ≤ targetFuel := by
      by_contra exceeds
      obtain ⟨history, running, _action⟩ := site.2
      exact running (targetBounded history.1.state history.1.trace (by
        rw [common history]
        omega))
    have rational := consistent.rationalAt_of_localOptimal targetRecall who (targetClock who)
      targetFuel (fun history => utility (targetObserve history) who) (by
        intro current atDepth uniformDepth _before law
        rw [target.continuationContext_remaining N targetFuel targetBounded who current
          atDepth uniformDepth]
        exact localOptimal who current law) site depth common within
    rwa [target.continuationContext_remaining N targetFuel targetBounded who site depth common]
      at rational
  · apply pmf_ext_toReal
    intro outcome
    let indicator (observed : Outcome) := ((PMF.pure observed) outcome).toReal
    have sourceLimit := M.runBehavioralFrom_expect_tendsto (sourceSequence 0) sourceMixed
      (fun n => (sourceSequence n).strategy) source.strategy sourceConverges.strategy
      (fun history => indicator (sourceObserve history)) sourceFuel E.initHistory
    have targetLimit := N.runBehavioralFrom_expect_tendsto (targetSequence (index 0))
      (targetMixed (index 0)) (fun n => (targetSequence (index n)).strategy) target.strategy
      targetConverges.strategy (fun history => indicator (targetObserve history))
      targetFuel T.initHistory
    have same (n : ℕ) :
        expect (N.runBehavioral (targetSequence (index n)).strategy targetFuel)
            (fun history => indicator (targetObserve history)) =
          expect (M.runBehavioral (sourceSequence (index n)).strategy sourceFuel)
            (fun history => indicator (sourceObserve history)) := by
      have mapped := congrArg (fun distribution => expect distribution indicator)
        (initialized (index n))
      simpa only [expect_map] using mapped
    have limits := tendsto_nhds_unique targetLimit
      ((sourceLimit.comp increasing.tendsto_atTop).congr'
        (Eventually.of_forall fun n => (same n).symm))
    calc
      (((N.runBehavioral target.strategy targetFuel).map targetObserve) outcome).toReal =
          expect (N.runBehavioral target.strategy targetFuel)
            (fun history => indicator (targetObserve history)) := by
        rw [← FinDist.expect_prob_pure, expect_map]
      _ = expect (M.runBehavioral source.strategy sourceFuel)
          (fun history => indicator (sourceObserve history)) := limits
      _ = (((M.runBehavioral source.strategy sourceFuel).map sourceObserve) outcome).toReal := by
        rw [← FinDist.expect_prob_pure, expect_map]

/-- Local target gains bounded by original-source gain mixtures, up to one
uniformly vanishing error, construct a single consistent target sequential
equilibrium. Mixtures may depend on the perturbation, site, and local lottery;
the source and target games and utilities remain fixed. An error-bound-only
branch covers harmless implementation choices with no source decision site.

The bounded target horizon covers completion. The source conclusion is its law
at the stated source fuel; choosing an adequate source horizon makes this a
terminal-law theorem. -/
theorem exists_sequentialEquilibrium_limit_of_local_comparisons
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (targetClock : ∀ who (site : N.InformationSite who),
      ∃ depth, InformationSite.CommonDepth N site depth)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceMixed : (sourceSequence 0).IsFullyMixed)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalWithin
      (fun who history => utility (sourceObserve history) who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
      targetRecall.decisionInformationAntichain)
    (comparisonError : ℕ → ℝ)
    (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (localComparisons : ∀ n who (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)),
      let comparison := N.assessmentComparison targetObserve targetFuel (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := M.assessmentComparison sourceObserve sourceFuel
                (sourceSequence n) who deviation
              expect sourceComparison.alternative (utility · who) -
                expect sourceComparison.prescribed (utility · who)) + comparisonError n)
    (initialized : ∀ n,
      (N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve =
        (M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.continuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve ∧
      ∃ index : ℕ → ℕ, StrictMono index ∧
        BehavioralAssessmentConvergesPointwise (fun n => targetSequence (index n)) target := by
  classical
  obtain ⟨target, index, increasing, targetConverges, consistent⟩ :=
    BehavioralAssessment.exists_sequentiallyConsistent_subsequence targetRecall.decisionInformationAntichain
      targetSequence targetMixed targetBayes
  have result := sequentialEquilibrium_of_local_comparisons_limit sourceObserve targetObserve
    sourceFuel targetFuel targetBounded targetRecall targetClock utility source sourceSequence
    sourceMixed sourceConverges sourceRational targetSequence targetMixed
    comparisonError errorVanishes localComparisons initialized target index increasing
    targetConverges consistent
  exact ⟨target, result.1, result.2, index, increasing, targetConverges⟩

/-- Exact local law-pair simulations are the zero-error case. Both laws must
use the same mixture of original source comparisons; harmless choices may
instead preserve their observed continuation law directly. -/
theorem exists_sequentialEquilibrium_limit_of_local_simulations
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (targetClock : ∀ who (site : N.InformationSite who),
      ∃ depth, InformationSite.CommonDepth N site depth)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceMixed : (sourceSequence 0).IsFullyMixed)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalWithin
      (fun who history => utility (sourceObserve history) who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
      targetRecall.decisionInformationAntichain)
    (localSimulations : ∀ n who (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)),
      let comparison := N.assessmentComparison targetObserve targetFuel (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      comparison.alternative = comparison.prescribed ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          comparison.prescribed = mixture.bind (fun deviation =>
            (M.assessmentComparison sourceObserve sourceFuel (sourceSequence n)
              who deviation).prescribed) ∧
          comparison.alternative = mixture.bind (fun deviation =>
            (M.assessmentComparison sourceObserve sourceFuel (sourceSequence n)
              who deviation).alternative))
    (initialized : ∀ n,
      (N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve =
        (M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.continuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve ∧
      ∃ index : ℕ → ℕ, StrictMono index ∧
        BehavioralAssessmentConvergesPointwise (fun n => targetSequence (index n)) target := by
  apply exists_sequentialEquilibrium_limit_of_local_comparisons sourceObserve targetObserve
    sourceFuel targetFuel targetBounded targetRecall targetClock utility source sourceSequence
    sourceMixed sourceConverges sourceRational targetSequence targetMixed targetBayes
    (fun _ => 0) tendsto_const_nhds ?_ initialized
  intro n who site law
  rcases localSimulations n who site law with harmless | ⟨mixture, prescribed, alternate⟩
  · left
    simp only [harmless, sub_self, le_refl]
  · right
    refine ⟨mixture, ?_⟩
    rw [alternate, prescribed, FinDist.expect_bind, FinDist.expect_bind]
    simp only [FinDist.expect_sub, add_zero, le_refl]

end GameTheory.ContinuationSimulation
