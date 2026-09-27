/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.UniformPolicyLimit
import GameTheoryExtensions.Protocol.ContinuationSimulation

/-! # Sequential equilibrium from simulations along a common perturbation

Private-history aggregation may choose different simulated source continuations
at each perturbation. Exact finite-mixture simulation at those fully mixed
assessments still suffices: uniform source regret vanishes, and one common
target subsequence supplies both consistent beliefs and sequential rationality.

The theorem does not assume a target equilibrium or its rationality. Constructing
the target perturbations and the exact continuation-law certificates remains
an operational obligation of the particular abstraction.
-/

noncomputable section

namespace GameTheory.ContinuationSimulation

open Protocol Protocol.InformationModel Protocol.ExecutionProtocol Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite E.History] [Finite T.History]
  [∀ who (site : N.InformationSite who), Fintype (N.InformationHistory who site.1)]

/-- A common sequence of exact continuation simulations yields an actual
target SE. The initialized law is retained separately and exactly; it may
include private types and every public result rather than only utilities. -/
theorem exists_sequentialEquilibrium_limit
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat) (targetAntichain : N.DecisionInformationAntichain)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceMixed : (sourceSequence 0).IsFullyMixed)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalWithin
      (fun who history => utility (sourceObserve history) who) sourceFuel)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
      targetAntichain)
    (simulations : ∀ n, ContinuationSimulation
      (M.assessmentComparison sourceObserve sourceFuel (sourceSequence n))
      (N.assessmentComparison targetObserve targetFuel (targetSequence n)))
    (initialized : ∀ n,
      (N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve =
        (M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetAntichain
        (fun who site => target.continuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve := by
  classical
  obtain ⟨target, index, increasing, targetConverges, consistent⟩ :=
    BehavioralAssessment.exists_sequentiallyConsistent_subsequence targetAntichain targetSequence
      targetMixed targetBayes
  refine ⟨target, ⟨?_, consistent⟩, ?_⟩
  · intro who site alternative _
    obtain ⟨error, _nonnegative, vanishes, bound⟩ :=
      sourceConverges.exists_uniform_policy_gain_bound (sourceSequence 0) sourceMixed
        who (fun history => utility (sourceObserve history) who) sourceFuel (sourceRational who)
    have sourceBound (n : ℕ) (deviation : M.AssessmentDeviation who) :
        ((M.assessmentComparison sourceObserve sourceFuel (sourceSequence n)
          who deviation).alternative).expect (utility · who) -
          ((M.assessmentComparison sourceObserve sourceFuel (sourceSequence n)
            who deviation).prescribed).expect (utility · who) ≤ error n := by
      simpa only [assessmentComparison, FinDist.expect_map, Context.value,
        BehavioralAssessment.continuationContext] using bound n deviation.1 deviation.2
    have targetBound (n : ℕ) :
        ((targetSequence n).continuationContext site
            (fun history => utility (targetObserve history) who) targetFuel).value alternative -
          ((targetSequence n).continuationContext site
            (fun history => utility (targetObserve history) who) targetFuel).value
              ((targetSequence n).strategy who) ≤ error n := by
      have estimate := FinDist.expect_mono
        (μ := (simulations n).alternatives who (site, alternative))
        (fun deviation _ => sourceBound n deviation)
      rw [FinDist.expect_const, FinDist.expect_sub] at estimate
      have comparison :
          ((N.assessmentComparison targetObserve targetFuel (targetSequence n) who
              (site, alternative)).alternative).expect (utility · who) -
            ((N.assessmentComparison targetObserve targetFuel (targetSequence n) who
              (site, alternative)).prescribed).expect (utility · who) ≤ error n := by
        rw [(simulations n).alternative, (simulations n).prescribed,
          FinDist.expect_bind, FinDist.expect_bind]
        exact estimate
      simpa only [assessmentComparison, FinDist.expect_map, Context.value,
        BehavioralAssessment.continuationContext] using comparison
    have alternate := targetConverges.context_value (targetSequence (index 0))
      (targetMixed (index 0)) site (fun history => utility (targetObserve history) who)
        targetFuel (fun _ => alternative) alternative
          (fun _ => finDistConvergesPointwise_const _)
    have prescribed := targetConverges.context_value (targetSequence (index 0))
      (targetMixed (index 0)) site (fun history => utility (targetObserve history) who)
        targetFuel (fun n => (targetSequence (index n)).strategy who) (target.strategy who)
          (targetConverges.strategy who)
    exact sub_nonpos.mp (le_of_tendsto_of_tendsto (alternate.sub prescribed)
      (vanishes.comp increasing.tendsto_atTop)
      (Eventually.of_forall fun n => targetBound (index n)))
  · apply FinDist.ext_of_prob
    intro outcome
    let indicator (observed : Outcome) := (FinDist.pure observed).prob outcome
    have sourceLimit := M.runBehavioralFrom_expect_tendsto (sourceSequence 0) sourceMixed
      (fun n => (sourceSequence n).strategy) source.strategy sourceConverges.strategy
      (fun history => indicator (sourceObserve history)) sourceFuel E.initHistory
    have targetLimit := N.runBehavioralFrom_expect_tendsto (targetSequence (index 0))
      (targetMixed (index 0)) (fun n => (targetSequence (index n)).strategy) target.strategy
      targetConverges.strategy (fun history => indicator (targetObserve history))
      targetFuel T.initHistory
    have same (n : ℕ) :
        (N.runBehavioral (targetSequence (index n)).strategy targetFuel).expect
            (fun history => indicator (targetObserve history)) =
          (M.runBehavioral (sourceSequence (index n)).strategy sourceFuel).expect
            (fun history => indicator (sourceObserve history)) := by
      have mapped := congrArg (fun law => law.expect indicator) (initialized (index n))
      simpa only [FinDist.expect_map] using mapped
    have limits := tendsto_nhds_unique targetLimit
      ((sourceLimit.comp increasing.tendsto_atTop).congr'
        (Eventually.of_forall fun n => (same n).symm))
    calc
      ((N.runBehavioral target.strategy targetFuel).map targetObserve).prob outcome =
          (N.runBehavioral target.strategy targetFuel).expect
            (fun history => indicator (targetObserve history)) := by
        rw [← FinDist.expect_prob_pure, FinDist.expect_map]
      _ = (M.runBehavioral source.strategy sourceFuel).expect
          (fun history => indicator (sourceObserve history)) := limits
      _ = ((M.runBehavioral source.strategy sourceFuel).map sourceObserve).prob outcome := by
        rw [← FinDist.expect_prob_pure, FinDist.expect_map]

end GameTheory.ContinuationSimulation
