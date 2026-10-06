/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.SequentialOneShot
import GameTheoryExtensions.Protocol.ContinuationHorizon
import GameTheoryExtensions.Analysis.Protocol.UniformPolicyLimit
import GameTheory.Analysis.Protocol.Incentives
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Sequential equilibrium from local continuation comparisons

Only local target deviations need a simulation, up to a uniformly vanishing
gain error. A local choice can instead have gain bounded by that same error.
This includes private response aliases at implementation-only decision sites.

All comparisons use the original source assessment sequence. Intermediate
behavioral realizations need neither be equilibria nor converge at unreachable
information sets. One common target subsequence supplies consistent beliefs;
decision recall then upgrades limiting local optimality to whole-policy SE by
the one-shot deviation principle, with no common decision clock.

The comparisons may be restricted to a set of copied information sites, provided
the limit is optimal at every other site by some separate argument such as
rational completion.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite E.History] [Finite T.History]
  [∀ who, DecidableEq (N.InfoState who)]

/-- Sequential rationality at a common consistent assessment limit, from local
comparisons at copied information sites and optimality of the limit at the
remaining free sites. At a copied site, every local target gain is bounded by an
original-source gain mixture, up to one uniformly vanishing error. Mixtures may
depend on the perturbation, site, and local lottery; the source and target games
and utilities remain fixed. An error-bound-only branch covers harmless
implementation choices with no source decision site. At a free site the limit
itself must already be optimal against single-site law changes, as rational
completion supplies; no comparison with the source is required there.

The perturbed target laws need only approach the perturbed source laws: every
observed outcome's probability may differ by a uniformly vanishing error. A
total-variation bound gives this. The limit laws then agree exactly.

The bounded target horizon covers completion. The source conclusion is its law
at the stated source fuel; choosing an adequate source horizon makes this a
terminal-law theorem. -/
theorem sequentialEquilibrium_of_copied_comparisons_limit_of_lawError
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (copied : ∀ who, N.InformationSite who → Prop)
    (comparisonError : ℕ → ℝ)
    (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (localComparisons : ∀ n who (site : N.InformationSite who), copied who site →
      ∀ law : PMF (N.Choice who site.1),
      let comparison := N.assessmentComparisonWith (N.truncatedRunner
          targetFuel) targetObserve (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                  sourceFuel) sourceObserve
                (sourceSequence n) who deviation
              expect sourceComparison.alternative (utility · who) -
                expect sourceComparison.prescribed (utility · who)) + comparisonError n)
    (lawError : ℕ → ℝ) (lawErrorVanishes : Tendsto lawError atTop (nhds 0))
    (initialized : ∀ n outcome,
      |(((N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve)
          outcome).toReal -
        (((M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve)
          outcome).toReal| ≤ lawError n)
    (target : N.BehavioralAssessment) (index : ℕ → ℕ) (increasing : StrictMono index)
    (targetConverges : BehavioralAssessmentConvergesPointwise
      (fun n => targetSequence (index n)) target)
    (consistent : target.IsSequentiallyConsistent targetRecall.decisionInformationAntichain)
    (freeOptimal : ∀ who (site : N.InformationSite who), ¬ copied who site →
      ∀ law : PMF (N.Choice who site.1),
        (target.truncatedContinuationContext site
            (fun history => utility (targetObserve history) who) targetFuel).value
              ((target.strategy who).withLaw site.1 law) ≤
          (target.truncatedContinuationContext site
            (fun history => utility (targetObserve history) who) targetFuel).value
              (target.strategy who)) :
    target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve := by
  classical
  have sourceTransitions : E.FiniteTransitions := .of_finite_history
  have targetTransitions : T.FiniteTransitions := .of_finite_history
  have localOptimal (who : Player) (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)) :
      (target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel).value
            ((target.strategy who).withLaw site.1 law) ≤
        (target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel).value
            (target.strategy who) := by
    by_cases kept : copied who site
    swap
    · exact freeOptimal who site kept law
    obtain ⟨error, nonnegative, vanishes, bound⟩ :=
      sourceConverges.exists_uniform_policy_gain_bound
        who (fun history => utility (sourceObserve history) who) sourceFuel (sourceRational who)
    obtain ⟨largest, largestBound⟩ :=
      (Set.finite_range fun history : E.History => |utility (sourceObserve history) who|).bddAbove
    have bounded (history : E.History) : |utility (sourceObserve history) who| ≤ largest :=
      largestBound ⟨history, rfl⟩
    have largestNonnegative : 0 ≤ largest := (abs_nonneg _).trans (bounded E.initHistory)
    have sourceGainBounded (n : ℕ) (deviation : M.AssessmentDeviation who) :
        |expect ((M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
            (sourceSequence n)
          who deviation).alternative) (utility · who) -
          expect ((M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
              (sourceSequence n)
            who deviation).prescribed) (utility · who)| ≤ 2 * largest := by
      simp only [assessmentComparisonWith, expect_map, Function.comp_def]
      have first := expect_abs_le_of_bounded
        (μ := M.assessmentLawWith (M.truncatedRunner sourceFuel) (sourceSequence n) deviation.1
            deviation.2)
        largestNonnegative bounded
      have second := expect_abs_le_of_bounded
        (μ := M.assessmentLawWith (M.truncatedRunner sourceFuel) (sourceSequence n) deviation.1
          ((sourceSequence n).strategy who))
        largestNonnegative bounded
      exact (abs_sub _ _).trans (by linarith)
    have sourceBound (n : ℕ) (deviation : M.AssessmentDeviation who) :
        expect ((M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
            (sourceSequence n)
          who deviation).alternative) (utility · who) -
          expect ((M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
              (sourceSequence n)
            who deviation).prescribed) (utility · who) ≤ error n := by
      simp only [assessmentComparisonWith, expect_map]
      exact bound n deviation.1 deviation.2
    have targetBound (n : ℕ) :
        ((targetSequence n).truncatedContinuationContext site
            (fun history => utility (targetObserve history) who) targetFuel).value
              (((targetSequence n).strategy who).withLaw site.1 law) -
          ((targetSequence n).truncatedContinuationContext site
            (fun history => utility (targetObserve history) who) targetFuel).value
              ((targetSequence n).strategy who) ≤ error n + comparisonError n := by
      have comparison :
          expect ((N.assessmentComparisonWith (N.truncatedRunner targetFuel) targetObserve
              (targetSequence n) who
              (site, ((targetSequence n).strategy who).withLaw site.1 law)).alternative)
                (utility · who) -
            expect ((N.assessmentComparisonWith (N.truncatedRunner targetFuel) targetObserve
                (targetSequence n) who
              (site, ((targetSequence n).strategy who).withLaw site.1 law)).prescribed)
                (utility · who) ≤ error n + comparisonError n := by
        rcases localComparisons n who site kept law with harmless | ⟨mixture, comparison⟩
        · exact harmless.trans (le_add_of_nonneg_left (nonnegative n))
        · dsimp only at comparison ⊢
          apply comparison.trans
          have estimate := expect_le_const mixture _
            (payoffIntegrable_of_bounded mixture _ (C := 2 * largest)
              fun deviation => sourceGainBounded n deviation)
            (error n) fun deviation _ => sourceBound n deviation
          linarith
      simp only [assessmentComparisonWith, expect_map] at comparison
      exact comparison
    have alternate := targetConverges.context_value targetTransitions
      site (fun history => utility (targetObserve history) who)
      targetFuel (fun n => ((targetSequence (index n)).strategy who).withLaw site.1 law)
      ((target.strategy who).withLaw site.1 law) (by
        intro decision
        by_cases same : decision = site
        · subst decision
          simpa only [BehavioralPolicy.withLaw_self] using pmfConvergesPointwise_const law
        · have different : decision.1 ≠ site.1 := fun equal => same (Subtype.ext equal)
          simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
            targetConverges.strategy who decision)
    have prescribed := targetConverges.context_value targetTransitions
      site (fun history => utility (targetObserve history) who)
        targetFuel (fun n => (targetSequence (index n)).strategy who) (target.strategy who)
          (targetConverges.strategy who)
    exact sub_nonpos.mp (le_of_tendsto_of_tendsto (alternate.sub prescribed)
      (by simpa only [zero_add, Function.comp_def] using
        (vanishes.add errorVanishes).comp increasing.tendsto_atTop)
      (Eventually.of_forall fun n => targetBound (index n)))
  have certificate := targetBounded.wellFoundedHistories
  have terminal : target.IsSequentialEquilibrium targetRecall.decisionInformationAntichain
      certificate (fun who history => utility (targetObserve history) who) := by
    refine (target.isSequentialEquilibrium_iff_locallyOptimal N targetRecall certificate _).mpr
      ⟨consistent, fun who site law => ?_⟩
    rw [target.continuationContext_eq_truncated_of_bounded certificate targetBounded]
    exact localOptimal who site law
  refine ⟨(target.isSequentialEquilibrium_iff_truncated_of_bounded N _ certificate targetBounded
    _).mp terminal, ?_⟩
  · apply pmf_ext_toReal
    intro outcome
    let indicator (observed : Outcome) : ℝ := if outcome = observed then 1 else 0
    have sourceLimit := M.runBehavioralFrom_expect_tendsto sourceTransitions
      (fun n => (sourceSequence n).strategy) source.strategy sourceConverges.strategy
      (fun history => indicator (sourceObserve history)) sourceFuel E.initHistory
    have targetLimit := N.runBehavioralFrom_expect_tendsto targetTransitions
      (fun n => (targetSequence (index n)).strategy) target.strategy
      targetConverges.strategy (fun history => indicator (targetObserve history))
      targetFuel T.initHistory
    have close (n : ℕ) :
        |expect (N.runBehavioral (targetSequence (index n)).strategy targetFuel)
            (fun history => indicator (targetObserve history)) -
          expect (M.runBehavioral (sourceSequence (index n)).strategy sourceFuel)
            (fun history => indicator (sourceObserve history))| ≤ lawError (index n) := by
      have bound := initialized (index n) outcome
      rwa [toReal_map_apply, toReal_map_apply] at bound
    have differenceVanishes : Tendsto (fun n =>
        expect (N.runBehavioral (targetSequence (index n)).strategy targetFuel)
            (fun history => indicator (targetObserve history)) -
          expect (M.runBehavioral (sourceSequence (index n)).strategy sourceFuel)
            (fun history => indicator (sourceObserve history))) atTop (nhds 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact close n)
        (lawErrorVanishes.comp increasing.tendsto_atTop)
    have limits := sub_eq_zero.mp (tendsto_nhds_unique
      (targetLimit.sub (sourceLimit.comp increasing.tendsto_atTop)) differenceVanishes)
    calc
      (((N.runBehavioral target.strategy targetFuel).map targetObserve) outcome).toReal =
          expect (N.runBehavioral target.strategy targetFuel)
            (fun history => indicator (targetObserve history)) :=
        toReal_map_apply _ _ _
      _ = expect (M.runBehavioral source.strategy sourceFuel)
          (fun history => indicator (sourceObserve history)) := limits
      _ = (((M.runBehavioral source.strategy sourceFuel).map sourceObserve) outcome).toReal :=
        (toReal_map_apply _ _ _).symm

/-- Local target gains bounded by original-source gain mixtures, up to one
uniformly vanishing error, preserve sequential rationality at a common consistent
assessment limit: the case of
`sequentialEquilibrium_of_copied_comparisons_limit_of_lawError` in which every
information site is copied. -/
theorem sequentialEquilibrium_of_local_comparisons_limit_of_lawError
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (comparisonError : ℕ → ℝ)
    (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (localComparisons : ∀ n who (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)),
      let comparison := N.assessmentComparisonWith (N.truncatedRunner
          targetFuel) targetObserve (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                  sourceFuel) sourceObserve
                (sourceSequence n) who deviation
              expect sourceComparison.alternative (utility · who) -
                expect sourceComparison.prescribed (utility · who)) + comparisonError n)
    (lawError : ℕ → ℝ) (lawErrorVanishes : Tendsto lawError atTop (nhds 0))
    (initialized : ∀ n outcome,
      |(((N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve)
          outcome).toReal -
        (((M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve)
          outcome).toReal| ≤ lawError n)
    (target : N.BehavioralAssessment) (index : ℕ → ℕ) (increasing : StrictMono index)
    (targetConverges : BehavioralAssessmentConvergesPointwise
      (fun n => targetSequence (index n)) target)
    (consistent : target.IsSequentiallyConsistent targetRecall.decisionInformationAntichain) :
    target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve :=
  sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve targetObserve
    sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational targetSequence (fun _ _ => True) comparisonError
    errorVanishes (fun n who site _ law => localComparisons n who site law) lawError
    lawErrorVanishes initialized target index increasing targetConverges consistent
    (fun _ _ free => absurd trivial free)

/-- The exact-law case of `sequentialEquilibrium_of_local_comparisons_limit_of_lawError`: the
perturbed target laws equal the perturbed source laws. -/
theorem sequentialEquilibrium_of_local_comparisons_limit
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (comparisonError : ℕ → ℝ)
    (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (localComparisons : ∀ n who (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)),
      let comparison := N.assessmentComparisonWith (N.truncatedRunner
          targetFuel) targetObserve (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                  sourceFuel) sourceObserve
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
        (fun who site => target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve :=
  sequentialEquilibrium_of_local_comparisons_limit_of_lawError sourceObserve targetObserve
    sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational targetSequence comparisonError errorVanishes localComparisons
    (fun _ => 0) tendsto_const_nhds
    (fun n outcome => by rw [initialized n, sub_self, abs_zero]) target index increasing
    targetConverges consistent

/-- Local target gains bounded by original-source gain mixtures, up to one
uniformly vanishing error, construct a single consistent target sequential
equilibrium. Mixtures may depend on the perturbation, site, and local lottery;
the source and target games and utilities remain fixed. An error-bound-only
branch covers harmless implementation choices with no source decision site.
The perturbed target laws need only approach the perturbed source laws, by a
uniformly vanishing error in every observed outcome's probability.

The bounded target horizon covers completion. The source conclusion is its law
at the stated source fuel; choosing an adequate source horizon makes this a
terminal-law theorem. -/
theorem exists_sequentialEquilibrium_limit_of_local_comparisons_of_lawError
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
      targetRecall.decisionInformationAntichain)
    (comparisonError : ℕ → ℝ)
    (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (localComparisons : ∀ n who (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)),
      let comparison := N.assessmentComparisonWith (N.truncatedRunner
          targetFuel) targetObserve (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                  sourceFuel) sourceObserve
                (sourceSequence n) who deviation
              expect sourceComparison.alternative (utility · who) -
                expect sourceComparison.prescribed (utility · who)) + comparisonError n)
    (lawError : ℕ → ℝ) (lawErrorVanishes : Tendsto lawError atTop (nhds 0))
    (initialized : ∀ n outcome,
      |(((N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve)
          outcome).toReal -
        (((M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve)
          outcome).toReal| ≤ lawError n) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve ∧
      ∃ index : ℕ → ℕ, StrictMono index ∧
        BehavioralAssessmentConvergesPointwise (fun n => targetSequence (index n)) target := by
  classical
  obtain ⟨target, index, increasing, targetConverges, consistent⟩ :=
    BehavioralAssessment.exists_sequentiallyConsistent_subsequence
      targetRecall.decisionInformationAntichain
      targetSequence targetMixed targetBayes
  have result := sequentialEquilibrium_of_local_comparisons_limit_of_lawError sourceObserve
    targetObserve sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational targetSequence
    comparisonError errorVanishes localComparisons lawError lawErrorVanishes initialized target
    index increasing targetConverges consistent
  exact ⟨target, result.1, result.2, index, increasing, targetConverges⟩

/-- The exact-law case of `exists_sequentialEquilibrium_limit_of_local_comparisons_of_lawError`:
the perturbed target laws equal the perturbed source laws. -/
theorem exists_sequentialEquilibrium_limit_of_local_comparisons
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
      targetRecall.decisionInformationAntichain)
    (comparisonError : ℕ → ℝ)
    (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (localComparisons : ∀ n who (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)),
      let comparison := N.assessmentComparisonWith (N.truncatedRunner
          targetFuel) targetObserve (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                  sourceFuel) sourceObserve
                (sourceSequence n) who deviation
              expect sourceComparison.alternative (utility · who) -
                expect sourceComparison.prescribed (utility · who)) + comparisonError n)
    (initialized : ∀ n,
      (N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve =
        (M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve ∧
      ∃ index : ℕ → ℕ, StrictMono index ∧
        BehavioralAssessmentConvergesPointwise (fun n => targetSequence (index n)) target :=
  exists_sequentialEquilibrium_limit_of_local_comparisons_of_lawError sourceObserve
    targetObserve sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational targetSequence targetMixed targetBayes comparisonError
    errorVanishes localComparisons (fun _ => 0) tendsto_const_nhds
    (fun n outcome => by rw [initialized n, sub_self, abs_zero])

/-- Exact local law-pair simulations are the zero-error case. Both laws must
use the same mixture of original source comparisons; harmless choices may
instead preserve their observed continuation law directly. -/
theorem exists_sequentialEquilibrium_limit_of_local_simulations
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
      targetRecall.decisionInformationAntichain)
    (localSimulations : ∀ n who (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)),
      let comparison := N.assessmentComparisonWith (N.truncatedRunner
          targetFuel) targetObserve (targetSequence n)
        who (site, ((targetSequence n).strategy who).withLaw site.1 law)
      comparison.alternative = comparison.prescribed ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          comparison.prescribed = mixture.bind (fun deviation =>
            (M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
                (sourceSequence n)
              who deviation).prescribed) ∧
          comparison.alternative = mixture.bind (fun deviation =>
            (M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
                (sourceSequence n)
              who deviation).alternative))
    (initialized : ∀ n,
      (N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve =
        (M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve ∧
      ∃ index : ℕ → ℕ, StrictMono index ∧
        BehavioralAssessmentConvergesPointwise (fun n => targetSequence (index n)) target := by
  apply exists_sequentialEquilibrium_limit_of_local_comparisons sourceObserve targetObserve
    sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational targetSequence targetMixed targetBayes
    (fun _ => 0) tendsto_const_nhds ?_ initialized
  intro n who site law
  rcases localSimulations n who site law with harmless | ⟨mixture, prescribed, alternate⟩
  · left
    simp only [harmless, sub_self, le_refl]
  · right
    refine ⟨mixture, ?_⟩
    have observed (laws : M.AssessmentDeviation who → PMF Outcome)
        (mapped : ∀ deviation, (laws deviation).support ⊆ Set.range sourceObserve) :
        PayoffIntegrable (mixture.bind laws) (utility · who) :=
      payoffIntegrable_of_finite_support _ _ ((Set.finite_range sourceObserve).subset
        fun value member => by
          obtain ⟨deviation, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
          exact mapped deviation member)
    have ofMap (law : PMF E.History) : (law.map sourceObserve).support ⊆ Set.range sourceObserve :=
      fun value member => by
        obtain ⟨history, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        exact ⟨history, rfl⟩
    have alternateIntegrable : PayoffIntegrable (mixture.bind fun deviation =>
        (M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve (sourceSequence n)
            who
          deviation).alternative) (utility · who) :=
      observed _ fun _ => ofMap _
    have prescribedIntegrable : PayoffIntegrable (mixture.bind fun deviation =>
        (M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve (sourceSequence n)
            who
          deviation).prescribed) (utility · who) :=
      observed _ fun _ => ofMap _
    dsimp only
    rw [alternate, prescribed]
    rw [expect_bind_tower _ _ _ alternateIntegrable, expect_bind_tower _ _ _ prescribedIntegrable,
      ← expect_sub (payoffIntegrable_bind_conditionalExpectation _ _ _ alternateIntegrable)
        (payoffIntegrable_bind_conditionalExpectation _ _ _ prescribedIntegrable), add_zero]

end GameTheory.Protocol.InformationModel
