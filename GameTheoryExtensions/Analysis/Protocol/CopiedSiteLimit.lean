/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.RestrictionIncentives
import GameTheoryExtensions.Analysis.Protocol.ComponentCompletion
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit

/-! # Sequential equilibrium from comparisons at copied sites

Every information agent of a target game plays a mixture of finitely many
fully supported component laws, which may vary along a sequence, with weights
chosen together by rational completion in the agent normal form; agents may be
pooled to share their weights, so that a move chosen by the pool reveals
nothing that distinguishes its members
(`exists_sequentialEquilibrium_limit_of_pooled_comparisons_of_lawError`). Agents are
split in advance into free and compared ones. A free agent's limit components
span all of its laws, typically one choice per component trembled toward a
fixed reference with a vanishing weight, so its optimality at the limit comes
from rational completion alone. A copied agent has one component, a prescribed
law such as a compiled source strategy with vanishing trembles. An agent with
several components is confined to their mixtures: completion chooses among
them, for instance between waiting and acting with a prescribed law.

At every compared site, each single choice must have a local target gain that
is negligible, bounded by an original-source gain mixture, or bounded by the
gain of some mixture of that agent's components at the same index, each up to
a vanishing error. Gains are affine in the local law, so this covers every
local lottery. Since the weights are chosen by the completion, the comparisons
and the law approximation are required for every choice of weights that is
optimal among each agent's component mixtures at every index; their errors may
depend on it. One common subsequence then converges to a target
sequential equilibrium that has the source law and, at every agent whose
components converge, plays a mixture of the limit components.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite E.History] [Fintype T.History]
  [∀ who, DecidableEq (N.InfoState who)]

omit [Finite E.History] [Fintype T.History] in
/-- Continuation gains are affine in the local law: a bound on the gain of
every single choice bounds the gain of every local lottery. -/
private theorem withLaw_gain_le_of_choice_gain_le [Finite T.History]
    (actsOnce : N.ActsOnceWhereItMatters)
    (assessment : N.BehavioralAssessment) (certificate : T.WellFoundedHistories)
    {who : Player} (site : N.InformationSite who) (payoff : T.History → ℝ) (bound : ℝ)
    (choiceGain : ∀ choice : N.Choice who site.1,
      (assessment.continuationContext certificate site payoff).value
          ((assessment.strategy who).withLaw site.1 (PMF.pure choice)) -
        (assessment.continuationContext certificate site payoff).value
          (assessment.strategy who) ≤ bound)
    (law : PMF (N.Choice who site.1)) :
    (assessment.continuationContext certificate site payoff).value
        ((assessment.strategy who).withLaw site.1 law) -
      (assessment.continuationContext certificate site payoff).value
        (assessment.strategy who) ≤ bound := by
  let _ := Fintype.ofFinite T.History
  have : Finite (N.Choice who site.1) :=
    N.finite_choice_of_played (N.site_mem_playedInformation site)
  have expand (law : PMF (N.Choice who site.1)) :=
    BehavioralAssessment.continuationContext_withLaw_eq_expect actsOnce assessment certificate site
      (assessment.strategy who) law payoff
  rw [expand]
  have committed := expect_le_const law
    (fun choice => (assessment.continuationContext certificate site payoff).value
      ((assessment.strategy who).commit site.1 choice)) (payoffIntegrable_of_finite _ _)
    ((assessment.continuationContext certificate site payoff).value
      (assessment.strategy who) + bound) fun choice _ => by
        have single := choiceGain choice
        rw [expand, expect_pure] at single
        linarith
  linarith

omit [Finite E.History] [Fintype T.History] in
/-- **Trembling a local law costs little.** At any assessment, the local gain of
a law exceeds the gain of its mixture with weight `weight` on a reference law
by at most `2 * weight * bound`, where `bound` bounds the observed utility.
A choice whose component is that choice trembled toward a reference therefore
meets the component comparison with error `2 * weight * bound`. -/
theorem withLaw_comparison_gain_le_mix_add [Finite T.History] {Outcome : Type*} {fuel : Nat}
    (bounded : T.BoundedHorizon fuel) (actsOnce : N.ActsOnceWhereItMatters)
    (observe : T.History → Outcome) (utility : Outcome → Player → ℝ)
    (assessment : N.BehavioralAssessment) {who : Player} (site : N.InformationSite who)
    (reference law : PMF (N.Choice who site.1))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (bound : ℝ) (utilityBound : ∀ history, |utility (observe history) who| ≤ bound) :
    expect (N.assessmentComparisonWith (N.truncatedRunner fuel) observe assessment who
        (site, (assessment.strategy who).withLaw site.1 law)).alternative (utility · who) -
      expect (N.assessmentComparisonWith (N.truncatedRunner fuel) observe assessment who
        (site, (assessment.strategy who).withLaw site.1 law)).prescribed (utility · who) ≤
    expect (N.assessmentComparisonWith (N.truncatedRunner fuel) observe assessment who
        (site, (assessment.strategy who).withLaw site.1
          (mix weight nonnegative small reference law))).alternative (utility · who) -
      expect (N.assessmentComparisonWith (N.truncatedRunner fuel) observe assessment who
        (site, (assessment.strategy who).withLaw site.1
          (mix weight nonnegative small reference law))).prescribed (utility · who) +
      2 * weight * bound := by
  let certificate := bounded.wellFoundedHistories
  let payoff (history : T.History) : ℝ := utility (observe history) who
  have values (installed : PMF (N.Choice who site.1)) :
      expect (N.assessmentComparisonWith (N.truncatedRunner fuel) observe assessment who
          (site, (assessment.strategy who).withLaw site.1 installed)).alternative (utility · who) -
        expect (N.assessmentComparisonWith (N.truncatedRunner fuel) observe assessment who
          (site, (assessment.strategy who).withLaw site.1 installed)).prescribed (utility · who) =
      expect installed (fun choice => (assessment.continuationContext certificate site payoff).value
          ((assessment.strategy who).commit site.1 choice)) -
        (assessment.continuationContext certificate site payoff).value
          (assessment.strategy who) := by
    rw [← BehavioralAssessment.continuationContext_withLaw_eq_expect actsOnce assessment
      certificate site (assessment.strategy who) installed payoff,
      assessment.continuationContext_eq_truncated_of_bounded certificate bounded]
    simp only [assessmentComparisonWith, expect_map]
    rfl
  rw [values, values]
  have boundNonnegative : 0 ≤ bound := (abs_nonneg _).trans (utilityBound T.initHistory)
  have committed (choice : N.Choice who site.1) :
      |(assessment.continuationContext certificate site payoff).value
          ((assessment.strategy who).commit site.1 choice)| ≤ bound :=
    expect_abs_le_of_bounded boundNonnegative utilityBound
  have integrable (installed : PMF (N.Choice who site.1)) :=
    payoffIntegrable_of_bounded installed _ committed
  rw [expect_mix _ _ _ _ _ _ (integrable reference) (integrable law)]
  have upper := mul_le_mul_of_nonneg_left
    (abs_le.mp (expect_abs_le_of_bounded (μ := law) boundNonnegative committed)).2 nonnegative
  have lower := mul_le_mul_of_nonneg_left
    (abs_le.mp (expect_abs_le_of_bounded (μ := reference) boundNonnegative committed)).1
    nonnegative
  linarith

open Classical in
/-- **Sequential equilibrium with pooled component agents.** Every agent plays a
mixture of its fully supported components with the common weights of its pool,
the weights of all pools being chosen by pooled rational completion
(`exists_consistent_pooled_completion`): no common replacement of a pool's
weights raises the sum of its members' local continuation gains.
Pooling the agents that differ only in what a cheap-talk move should not reveal
makes those moves uninformative: all members move with one law.

The obligations may use these facts. Every site's component-mixture gains must
be at most a vanishing error (the member-rationality obligation): automatic for an agent alone in
its pool, and for a pool whose members share a nearly best part see
`pooled_member_le_of_common_best`. At a free agent the limit components
converge and span all local laws. At every other agent each single choice must
be negligible, bounded by an original-source gain mixture, or bounded by the
gain of some mixture of its own components, at the same index up to a
vanishing error. If the target observation laws approach the perturbed source
laws, a target sequential equilibrium exists that has the source law, plays at
every agent whose components converge a mixture of the limit components, and is
the limit of one subsequence of the perturbed family. -/
theorem exists_sequentialEquilibrium_limit_of_pooled_comparisons_of_lawError
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (fallback : ∀ who, N.Policy who)
    {Pool : Type*} [Finite Pool] [DecidableEq Pool]
    (pool : N.InformationAgent N.playedInformation → Pool)
    {Part : Pool → Type*} [∀ p, Finite (Part p)] [∀ p, Nonempty (Part p)]
    (component : ℕ → ∀ agent, Part (pool agent) →
      PMF ((N.agentForm fallback targetBounded.wellFoundedHistories).sig.Strategy agent))
    (componentFull : ∀ n agent part, FullSupport (component n agent part))
    (free : Finset (N.InformationAgent N.playedInformation))
    (freeSpanning : ∀ who (site : N.InformationSite who), N.agentAt site ∈ free →
      ∃ limitComponent : Part (pool (N.agentAt site)) → PMF (N.Choice who site.1),
        (∀ part, PMFConvergesPointwise (fun n => component n (N.agentAt site) part)
          (limitComponent part)) ∧
        ∀ law : PMF (N.Choice who site.1), ∃ weights : PMF (Part (pool (N.agentAt site))),
          weights.bind limitComponent = law)
    (memberRational :
      ∀ (weights : ℕ → ∀ p, PMF (Part p)) (targetSequence : ℕ → N.BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
          fun agent => (weights n (pool agent)).bind (component n agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
          targetRecall.decisionInformationAntichain) →
        (∀ n (alternative : ∀ p, PMF (Part p)) p,
          ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
            (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
              let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
                targetObserve (targetSequence n) agent.1
                (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (pool agent)).bind (component n agent)))
              expect comparison.alternative (utility · agent.1) -
                expect comparison.prescribed (utility · agent.1)
            else 0) ≤ 0) →
        ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
          ∀ n who (site : N.InformationSite who)
            (alternative : PMF (Part (pool (N.agentAt site)))),
            let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
              targetObserve (targetSequence n) who
              (site, ((targetSequence n).strategy who).withLaw site.1
                (alternative.bind (component n (N.agentAt site))))
            expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤ memberError n)
    (localComparisons :
      ∀ (weights : ℕ → ∀ p, PMF (Part p)) (targetSequence : ℕ → N.BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
          fun agent => (weights n (pool agent)).bind (component n agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
          targetRecall.decisionInformationAntichain) →
        (∀ n (alternative : ∀ p, PMF (Part p)) p,
          ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
            (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
              let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
                targetObserve (targetSequence n) agent.1
                (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (pool agent)).bind (component n agent)))
              expect comparison.alternative (utility · agent.1) -
                expect comparison.prescribed (utility · agent.1)
            else 0) ≤ 0) →
        ∃ comparisonError : ℕ → ℝ, Tendsto comparisonError atTop (nhds 0) ∧
          ∀ n who (site : N.InformationSite who), N.agentAt site ∉ free →
            ∀ choice : N.Choice who site.1,
            let gain := fun law : PMF (N.Choice who site.1) =>
              let comparison := N.assessmentComparisonWith (N.truncatedRunner
                  targetFuel) targetObserve (targetSequence n)
                who (site, ((targetSequence n).strategy who).withLaw site.1 law)
              expect comparison.alternative (utility · who) -
                expect comparison.prescribed (utility · who)
            gain (PMF.pure choice) ≤ comparisonError n ∨
              (∃ alternative : PMF (Part (pool (N.agentAt site))),
                gain (PMF.pure choice) ≤
                  gain (alternative.bind (component n (N.agentAt site))) + comparisonError n) ∨
              ∃ mixture : PMF (M.AssessmentDeviation who),
                gain (PMF.pure choice) ≤
                  expect mixture (fun deviation =>
                    let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                        sourceFuel) sourceObserve
                      (sourceSequence n) who deviation
                    expect sourceComparison.alternative (utility · who) -
                      expect sourceComparison.prescribed (utility · who)) + comparisonError n)
    (lawApproximation :
      ∀ (weights : ℕ → ∀ p, PMF (Part p)) (targetSequence : ℕ → N.BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
          fun agent => (weights n (pool agent)).bind (component n agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
          targetRecall.decisionInformationAntichain) →
        (∀ n (alternative : ∀ p, PMF (Part p)) p,
          ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
            (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
              let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
                targetObserve (targetSequence n) agent.1
                (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (pool agent)).bind (component n agent)))
              expect comparison.alternative (utility · agent.1) -
                expect comparison.prescribed (utility · agent.1)
            else 0) ≤ 0) →
        ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
          ∀ n outcome,
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
      (∀ who (site : N.InformationSite who)
          (limitComponent : Part (pool (N.agentAt site)) → PMF (N.Choice who site.1)),
        (∀ part, PMFConvergesPointwise (fun n => component n (N.agentAt site) part)
          (limitComponent part)) →
        ∃ limitWeights : PMF (Part (pool (N.agentAt site))),
          target.strategy who site.1 = limitWeights.bind limitComponent) ∧
      ∃ (weights : ℕ → ∀ p, PMF (Part p)) (index : ℕ → ℕ), StrictMono index ∧
        ∀ who (site : N.InformationSite who),
          PMFConvergesPointwise
            (fun n => N.agentBehavior N.playedInformation fallback
              (fun agent => (weights (index n) (pool agent)).bind (component (index n) agent))
              who site.1)
            (target.strategy who site.1) := by
  classical
  let certificate := targetBounded.wellFoundedHistories
  let payoff (who : Player) (history : T.History) : ℝ := utility (targetObserve history) who
  obtain ⟨weights, sequence, target, index, played, mixed, bayes, increasing, converges,
      consistent, pooledValue, limitFacts⟩ :=
    N.exists_consistent_pooled_completion targetRecall fallback certificate payoff pool component
      componentFull
  choose sourceError sourceNonnegative sourceVanishes sourceBound using fun who =>
    sourceConverges.exists_uniform_policy_gain_bound who
      (fun history => utility (sourceObserve history) who) sourceFuel (sourceRational who)
  let totalSourceError (n : ℕ) : ℝ := ∑ who, sourceError who n
  have totalNonnegative (n : ℕ) : 0 ≤ totalSourceError n :=
    Finset.sum_nonneg fun who _ => sourceNonnegative who n
  have totalVanishes : Tendsto totalSourceError atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun who _ => sourceVanishes who)
  have sourceLe (n : ℕ) (who : Player) : sourceError who n ≤ totalSourceError n :=
    Finset.single_le_sum (fun other _ => sourceNonnegative other n) (Finset.mem_univ who)
  have mixtureBound (n : ℕ) (who : Player) (mixture : PMF (M.AssessmentDeviation who)) :
      expect mixture (fun deviation =>
        expect (M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
            (sourceSequence n) who deviation).alternative (utility · who) -
          expect (M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
            (sourceSequence n) who deviation).prescribed (utility · who)) ≤
        sourceError who n := by
    obtain ⟨largest, largestBound⟩ :=
      (Set.finite_range fun history : E.History => |utility (sourceObserve history) who|).bddAbove
    have bounded (history : E.History) : |utility (sourceObserve history) who| ≤ largest :=
      largestBound ⟨history, rfl⟩
    have largestNonnegative : 0 ≤ largest := (abs_nonneg _).trans (bounded E.initHistory)
    have gainBounded (deviation : M.AssessmentDeviation who) :
        |expect (M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
            (sourceSequence n) who deviation).alternative (utility · who) -
          expect (M.assessmentComparisonWith (M.truncatedRunner sourceFuel) sourceObserve
            (sourceSequence n) who deviation).prescribed (utility · who)| ≤ 2 * largest := by
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
    refine expect_le_const mixture _
      (payoffIntegrable_of_bounded mixture _ (C := 2 * largest) gainBounded) _
      fun deviation _ => ?_
    simp only [assessmentComparisonWith, expect_map]
    exact sourceBound who n deviation.1 deviation.2
  have gainEq (n : ℕ) (who : Player) (site : N.InformationSite who)
      (law : PMF (N.Choice who site.1)) :
      expect (N.assessmentComparisonWith (N.truncatedRunner targetFuel) targetObserve
          (sequence n) who (site, ((sequence n).strategy who).withLaw site.1 law)).alternative
          (utility · who) -
        expect (N.assessmentComparisonWith (N.truncatedRunner targetFuel) targetObserve
          (sequence n) who (site, ((sequence n).strategy who).withLaw site.1 law)).prescribed
          (utility · who) =
      ((sequence n).continuationContext certificate site (payoff who)).value
          (((sequence n).strategy who).withLaw site.1 law) -
        ((sequence n).continuationContext certificate site (payoff who)).value
          ((sequence n).strategy who) := by
    rw [(sequence n).continuationContext_eq_truncated_of_bounded certificate targetBounded]
    simp only [assessmentComparisonWith, expect_map]
    rfl
  have pooled (n : ℕ) (alternative : ∀ p, PMF (Part p)) (p : Pool) :
      ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
        (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
          let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
            targetObserve (sequence n) agent.1
            (⟨agent.2.1, decision⟩, ((sequence n).strategy agent.1).withLaw agent.2.1
              ((alternative (pool agent)).bind (component n agent)))
          expect comparison.alternative (utility · agent.1) -
            expect comparison.prescribed (utility · agent.1)
        else 0) ≤ 0 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun agent _ => ?_))
      (pooledValue n alternative p)
    by_cases decision : N.IsDecisionInfo agent.1 agent.2.1
    · simp only [decision, ↓reduceDIte]
      exact gainEq n agent.1 ⟨agent.2.1, decision⟩ _
    · simp only [decision, ↓reduceDIte]
  obtain ⟨memberError, memberVanishes, memberBound⟩ :=
    memberRational weights sequence played mixed bayes pooled
  obtain ⟨comparisonError, errorVanishes, comparisons⟩ :=
    localComparisons weights sequence played mixed bayes pooled
  obtain ⟨lawError, lawErrorVanishes, approximation⟩ :=
    lawApproximation weights sequence played mixed bayes pooled
  have choiceBound (n : ℕ) (who : Player) (site : N.InformationSite who)
      (compared : N.agentAt site ∉ free) (choice : N.Choice who site.1) :
      ((sequence n).continuationContext certificate site (payoff who)).value
          (((sequence n).strategy who).withLaw site.1 (PMF.pure choice)) -
        ((sequence n).continuationContext certificate site (payoff who)).value
          ((sequence n).strategy who) ≤
        comparisonError n + memberError n + totalSourceError n := by
    have memberNonnegative : 0 ≤ memberError n := by
      have bound := memberBound n who site (weights n (pool (N.agentAt site)))
      dsimp only at bound
      rw [gainEq] at bound
      have current : (weights n (pool (N.agentAt site))).bind (component n (N.agentAt site)) =
          (sequence n).strategy who site.1 := by
        rw [played]
        exact (N.agentBehavior_at N.playedInformation fallback
          (fun agent => (weights n (pool agent)).bind (component n agent)) (N.agentAt site)).symm
      rw [current, BehavioralPolicy.withLaw_eq_self, sub_self] at bound
      exact bound
    rcases comparisons n who site compared choice with
      harmless | ⟨alternative, dominated⟩ | ⟨mixture, sourced⟩
    · dsimp only at harmless
      rw [gainEq] at harmless
      linarith [totalNonnegative n]
    · dsimp only at dominated
      rw [gainEq, gainEq] at dominated
      have member := memberBound n who site alternative
      dsimp only at member
      rw [gainEq] at member
      linarith [totalNonnegative n]
    · dsimp only at sourced
      rw [gainEq] at sourced
      linarith [mixtureBound n who mixture, sourceLe n who, memberNonnegative]
  have result := sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve
    targetObserve sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational sequence (fun _ site => N.agentAt site ∉ free)
    (fun n => comparisonError n + memberError n + totalSourceError n)
    (by simpa only [add_zero] using (errorVanishes.add memberVanishes).add totalVanishes)
    (fun n who site compared law => by
      dsimp only
      left
      rw [gainEq]
      exact withLaw_gain_le_of_choice_gain_le targetRecall.actsOnceWhereItMatters (sequence n)
        certificate site (payoff who) _ (choiceBound n who site compared) law)
    lawError lawErrorVanishes
    approximation target index increasing
    converges consistent (fun who site kept law => by
      obtain ⟨limitComponent, componentConverges, spanning⟩ :=
        freeSpanning who site (not_not.mp kept)
      obtain ⟨limitWeights, rfl⟩ := spanning law
      have optimal := (limitFacts who site limitComponent componentConverges).2 memberError
        memberVanishes (fun n alternative => by
          have bound := memberBound n who site alternative
          dsimp only at bound
          rw [gainEq] at bound
          linarith) limitWeights
      rwa [target.continuationContext_eq_truncated_of_bounded certificate targetBounded] at optimal)
  refine ⟨target, result.1, result.2, fun who site limitComponent componentConverges =>
    (limitFacts who site limitComponent componentConverges).1, weights, index, increasing,
    fun who site => ?_⟩
  simpa only [played] using converges.strategy who site

/-- **Sequential equilibrium with component agents.** Every agent plays a
mixture of its fully supported components with weights chosen by rational
completion. At a free agent the limit components converge and span all local
laws. At every other agent each single choice must satisfy one of three local
comparisons at the same index, uniformly over the completion's weights up to
a vanishing error: its target gain is negligible; or it is at most the gain of
some mixture of the agent's own components; or it is at most an
original-source gain mixture. The middle branch is free of source content:
the completion makes every component mixture's gain nonpositive at every
index. If, in addition, the target observation laws approach the perturbed
source laws, then a target sequential equilibrium exists that has the source
law, plays at every agent whose components converge a mixture of the limit
components, and is the limit of one subsequence of the perturbed family.

Both obligations may use that the weights are rational in this sense: at
every index and site, no mixture of the agent's components has positive local
gain. The law approximation in particular need not hold for weights that, say,
wait until a deadline passes when waiting is strictly worse.

The source assessment sequence and the source comparisons are those of
`sequentialEquilibrium_of_copied_comparisons_limit_of_lawError`. -/
theorem exists_sequentialEquilibrium_limit_of_component_comparisons_of_lawError
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (fallback : ∀ who, N.Policy who)
    {Component : N.InformationAgent N.playedInformation → Type*}
    [∀ agent, Finite (Component agent)] [∀ agent, Nonempty (Component agent)]
    (component : ℕ → ∀ agent, Component agent →
      PMF ((N.agentForm fallback targetBounded.wellFoundedHistories).sig.Strategy agent))
    (componentFull : ∀ n agent part, FullSupport (component n agent part))
    (free : Finset (N.InformationAgent N.playedInformation))
    (freeSpanning : ∀ who (site : N.InformationSite who), N.agentAt site ∈ free →
      ∃ limitComponent : Component (N.agentAt site) → PMF (N.Choice who site.1),
        (∀ part, PMFConvergesPointwise (fun n => component n (N.agentAt site) part)
          (limitComponent part)) ∧
        ∀ law : PMF (N.Choice who site.1), ∃ weights : PMF (Component (N.agentAt site)),
          weights.bind limitComponent = law)
    (localComparisons :
      ∀ (weights : ℕ → ∀ agent, PMF (Component agent))
        (targetSequence : ℕ → N.BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
          fun agent => (weights n agent).bind (component n agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
          targetRecall.decisionInformationAntichain) →
        (∀ n who (site : N.InformationSite who)
            (alternative : PMF (Component (N.agentAt site))),
          let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
            targetObserve (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (component n (N.agentAt site))))
          expect comparison.alternative (utility · who) ≤
            expect comparison.prescribed (utility · who)) →
        ∃ comparisonError : ℕ → ℝ, Tendsto comparisonError atTop (nhds 0) ∧
          ∀ n who (site : N.InformationSite who), N.agentAt site ∉ free →
            ∀ choice : N.Choice who site.1,
            let gain := fun law : PMF (N.Choice who site.1) =>
              let comparison := N.assessmentComparisonWith (N.truncatedRunner
                  targetFuel) targetObserve (targetSequence n)
                who (site, ((targetSequence n).strategy who).withLaw site.1 law)
              expect comparison.alternative (utility · who) -
                expect comparison.prescribed (utility · who)
            gain (PMF.pure choice) ≤ comparisonError n ∨
              (∃ alternative : PMF (Component (N.agentAt site)),
                gain (PMF.pure choice) ≤
                  gain (alternative.bind (component n (N.agentAt site))) + comparisonError n) ∨
              ∃ mixture : PMF (M.AssessmentDeviation who),
                gain (PMF.pure choice) ≤
                  expect mixture (fun deviation =>
                    let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                        sourceFuel) sourceObserve
                      (sourceSequence n) who deviation
                    expect sourceComparison.alternative (utility · who) -
                      expect sourceComparison.prescribed (utility · who)) + comparisonError n)
    (lawApproximation :
      ∀ (weights : ℕ → ∀ agent, PMF (Component agent))
        (targetSequence : ℕ → N.BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
          fun agent => (weights n agent).bind (component n agent)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
          targetRecall.decisionInformationAntichain) →
        (∀ n who (site : N.InformationSite who)
            (alternative : PMF (Component (N.agentAt site))),
          let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
            targetObserve (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (component n (N.agentAt site))))
          expect comparison.alternative (utility · who) ≤
            expect comparison.prescribed (utility · who)) →
        ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
          ∀ n outcome,
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
      (∀ who (site : N.InformationSite who)
          (limitComponent : Component (N.agentAt site) → PMF (N.Choice who site.1)),
        (∀ part, PMFConvergesPointwise (fun n => component n (N.agentAt site) part)
          (limitComponent part)) →
        ∃ limitWeights : PMF (Component (N.agentAt site)),
          target.strategy who site.1 = limitWeights.bind limitComponent) ∧
      ∃ (weights : ℕ → ∀ agent, PMF (Component agent)) (index : ℕ → ℕ), StrictMono index ∧
        ∀ who (site : N.InformationSite who),
          PMFConvergesPointwise
            (fun n => N.agentBehavior N.playedInformation fallback
              (fun agent => (weights (index n) agent).bind (component (index n) agent))
              who site.1)
            (target.strategy who site.1) := by
  classical
  refine exists_sequentialEquilibrium_limit_of_pooled_comparisons_of_lawError sourceObserve
    targetObserve sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational fallback (Part := Component) id component componentFull free
    freeSpanning ?_ ?_ ?_
  all_goals
    intro weights targetSequence played mixed bayes pooled
    have single (n : ℕ) (who : Player) (site : N.InformationSite who)
        (alternative : PMF (Component (N.agentAt site))) :
        let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
          targetObserve (targetSequence n) who
          (site, ((targetSequence n).strategy who).withLaw site.1
            (alternative.bind (component n (N.agentAt site))))
        expect comparison.alternative (utility · who) ≤
          expect comparison.prescribed (utility · who) := by
      have total := pooled n (Function.update (weights n) (N.agentAt site) alternative)
        (N.agentAt site)
      rw [show Finset.univ.filter (fun agent => id agent = N.agentAt site) = {N.agentAt site} by
        ext agent; simp, Finset.sum_singleton,
        show Function.update (weights n) (N.agentAt site) alternative (id (N.agentAt site)) =
          alternative from Function.update_self ..] at total
      simp only [show N.IsDecisionInfo (N.agentAt site).1 (N.agentAt site).2.1 from site.2,
        ↓reduceDIte] at total
      exact sub_nonpos.mp total
  · exact ⟨fun _ => 0, tendsto_const_nhds, fun n who site alternative => by
      have bound := single n who site alternative
      dsimp only at bound ⊢
      linarith⟩
  · exact localComparisons weights targetSequence played mixed bayes single
  · exact lawApproximation weights targetSequence played mixed bayes single

/-- **Sequential equilibrium with copied and free agents.** Copied agents (those
outside `free`) play `pinned`, which converges to `compiled`; free agents play
`epsilon`-trembles toward `reference` around residual laws chosen by rational
completion. If, for every choice of residual laws, local target gains at copied
sites are bounded by original-source gain mixtures up to a vanishing error, and
the target observation laws approach the perturbed source laws, then a target
sequential equilibrium exists that has the source law, agrees with `compiled` at
every copied site, and is the limit of one subsequence of the perturbed family.

This is the case of
`exists_sequentialEquilibrium_limit_of_component_comparisons_of_lawError` with
`pinnedTrembleComponent`: one component per choice, trembled toward
`reference`, at a free agent, and the pinned law at every other agent. The
comparisons are required for every local law; with `free` empty no residual law
is used. -/
theorem exists_sequentialEquilibrium_limit_of_copied_comparisons_of_lawError
    {Outcome : Type*} (sourceObserve : E.History → Outcome) (targetObserve : T.History → Outcome)
    (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ)
    (source : M.BehavioralAssessment) (sourceSequence : ℕ → M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel)
    (fallback : ∀ who, N.Policy who)
    (free : Finset (N.InformationAgent N.playedInformation))
    (pinned : ℕ → Profile (N.agentForm fallback targetBounded.wellFoundedHistories).sig.mixed)
    (reference : Profile (N.agentForm fallback targetBounded.wellFoundedHistories).sig.mixed)
    (pinnedFull : ∀ n agent, agent ∉ free → FullSupport (pinned n agent))
    (referenceFull : ∀ agent, FullSupport (reference agent))
    (epsilon : ℕ → ℝ) (positive : ∀ n, 0 < epsilon n) (small : ∀ n, epsilon n < 1)
    (vanishes : Tendsto epsilon atTop (nhds 0))
    (compiled : ∀ who, N.BehavioralPolicy who)
    (pinnedConverges : ∀ who (site : N.InformationSite who), N.agentAt site ∉ free →
      PMFConvergesPointwise (fun n => pinned n (N.agentAt site)) (compiled who site.1))
    (localComparisons :
      ∀ (residual : ℕ → Profile (N.agentForm fallback targetBounded.wellFoundedHistories).sig.mixed)
        (targetSequence : ℕ → N.BehavioralAssessment),
        (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
          (pinnedTremble free (pinned n) reference (residual n) (epsilon n) (positive n).le
            (small n).le)) →
        (∀ n, (targetSequence n).IsFullyMixed) →
        (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
          targetRecall.decisionInformationAntichain) →
        ∃ comparisonError : ℕ → ℝ, Tendsto comparisonError atTop (nhds 0) ∧
          ∀ n who (site : N.InformationSite who), N.agentAt site ∉ free →
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
    (lawApproximation :
      ∀ residual : ℕ → Profile (N.agentForm fallback targetBounded.wellFoundedHistories).sig.mixed,
        ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
          ∀ n outcome,
            |(((N.runBehavioral (N.agentBehavior N.playedInformation fallback
                  (pinnedTremble free (pinned n) reference (residual n) (epsilon n)
                    (positive n).le (small n).le)) targetFuel).map targetObserve)
                outcome).toReal -
              (((M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve)
                outcome).toReal| ≤ lawError n) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve ∧
      (∀ who (site : N.InformationSite who), N.agentAt site ∉ free →
        target.strategy who site.1 = compiled who site.1) ∧
      ∃ (residual : ℕ → Profile (N.agentForm fallback targetBounded.wellFoundedHistories).sig.mixed)
        (index : ℕ → ℕ), StrictMono index ∧
        ∀ who (site : N.InformationSite who),
          PMFConvergesPointwise
            (fun n => N.agentBehavior N.playedInformation fallback
              (pinnedTremble free (pinned (index n)) reference (residual (index n))
                (epsilon (index n)) (positive (index n)).le (small (index n)).le) who site.1)
            (target.strategy who site.1) := by
  classical
  let F := N.agentForm fallback targetBounded.wellFoundedHistories
  let component (n : ℕ) := pinnedTrembleComponent (F := F) free (pinned n) reference (epsilon n)
    (positive n).le (small n).le
  have _ (agent : N.InformationAgent N.playedInformation) : Finite (F.sig.Strategy agent) :=
    N.finite_choice_of_played agent.2.2
  have _ (agent : N.InformationAgent N.playedInformation) : Nonempty (F.sig.Strategy agent) :=
    N.nonempty_choice_of_played agent.2.2
  have assembled (n : ℕ) (residual : Profile F.sig.mixed) :
      (fun agent => (residual agent).bind (component n agent)) =
        pinnedTremble free (pinned n) reference residual (epsilon n) (positive n).le
          (small n).le :=
    funext fun agent => bind_pinnedTrembleComponent free (pinned n) reference residual
      (epsilon n) (positive n).le (small n).le agent
  have componentFull (n : ℕ) (agent : N.InformationAgent N.playedInformation)
      (choice : F.sig.Strategy agent) : FullSupport (component n agent choice) := by
    by_cases active : agent ∈ free
    · intro other
      simp only [component, pinnedTrembleComponent, active, ↓reduceIte]
      exact mem_support_mix_left _ _ _ (positive n) (referenceFull agent other)
    · simpa only [component, pinnedTrembleComponent, active, ↓reduceIte] using
        pinnedFull n agent active
  obtain ⟨target, equilibrium, law, mixtures, residual, index, increasing, convergence⟩ :=
    exists_sequentialEquilibrium_limit_of_component_comparisons_of_lawError sourceObserve
      targetObserve sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
      sourceConverges sourceRational fallback (Component := fun agent => F.sig.Strategy agent)
      component componentFull free
      (fun who site active => ⟨PMF.pure, fun choice => by
          simpa only [component, pinnedTrembleComponent, active, ↓reduceIte] using
            pmfConvergesPointwise_mix_zero epsilon (fun n => (positive n).le)
              (fun n => (small n).le) vanishes (reference (N.agentAt site)) (PMF.pure choice),
        fun law => ⟨law, PMF.bind_pure law⟩⟩)
      (fun weights targetSequence played mixed bayes _ => by
        have played' (n : ℕ) : (targetSequence n).strategy =
            N.agentBehavior N.playedInformation fallback
              (pinnedTremble free (pinned n) reference (weights n) (epsilon n) (positive n).le
                (small n).le) := by
          rw [played n, assembled]
        obtain ⟨comparisonError, errorVanishes, comparisons⟩ :=
          localComparisons weights targetSequence played' mixed bayes
        refine ⟨comparisonError, errorVanishes, fun n who site compared choice => ?_⟩
        rcases comparisons n who site compared (PMF.pure choice) with harmless | sourced
        · exact Or.inl harmless
        · exact Or.inr (Or.inr sourced))
      (fun weights targetSequence played _ _ _ => by
        obtain ⟨lawError, lawErrorVanishes, approximation⟩ := lawApproximation weights
        exact ⟨lawError, lawErrorVanishes, fun n outcome => by
          rw [played n, assembled]
          exact approximation n outcome⟩)
  refine ⟨target, equilibrium, law, fun who site compared => ?_, residual, index, increasing,
    fun who site => by simpa only [assembled] using convergence who site⟩
  obtain ⟨limitWeights, agrees⟩ := mixtures who site (fun _ => compiled who site.1)
    fun _ => by
      simpa only [component, pinnedTrembleComponent, compared, ↓reduceIte] using
        pinnedConverges who site compared
  rw [agrees, PMF.bind_const]

open Classical in
/-- **A pooled component family with its obligations.** The data and the
local and law obligations of
`exists_sequentialEquilibrium_limit_of_pooled_comparisons_of_lawError` for one
source assessment sequence: a fallback policy, pools of agents sharing weights,
fully supported components, the free agents with spanning limit components,
and the three obligations, each required for every weights family that the
pooled completion may choose. -/
structure PooledLimitCertificate {Outcome : Type*} (sourceObserve : E.History → Outcome)
    (targetObserve : T.History → Outcome) (sourceFuel targetFuel : Nat)
    (targetBounded : T.BoundedHorizon targetFuel) (targetRecall : N.DecisionRecall)
    (utility : Outcome → Player → ℝ) (sourceSequence : ℕ → M.BehavioralAssessment) where
  fallback : ∀ who, N.Policy who
  Pool : Type
  [poolFinite : Finite Pool]
  [poolDecidable : DecidableEq Pool]
  pool : N.InformationAgent N.playedInformation → Pool
  Part : Pool → Type
  [partFinite : ∀ p, Finite (Part p)]
  [partNonempty : ∀ p, Nonempty (Part p)]
  component : ℕ → ∀ agent, Part (pool agent) →
    PMF ((N.agentForm fallback targetBounded.wellFoundedHistories).sig.Strategy agent)
  componentFull : ∀ n agent part, FullSupport (component n agent part)
  free : Finset (N.InformationAgent N.playedInformation)
  freeSpanning : ∀ who (site : N.InformationSite who), N.agentAt site ∈ free →
    ∃ limitComponent : Part (pool (N.agentAt site)) → PMF (N.Choice who site.1),
      (∀ part, PMFConvergesPointwise (fun n => component n (N.agentAt site) part)
        (limitComponent part)) ∧
      ∀ law : PMF (N.Choice who site.1), ∃ weights : PMF (Part (pool (N.agentAt site))),
        weights.bind limitComponent = law
  memberRational : ∀ (weights : ℕ → ∀ p, PMF (Part p)) (targetSequence : ℕ →
      N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
              targetObserve (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool agent)).bind (component n agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who)
          (alternative : PMF (Part (pool (N.agentAt site)))),
          let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
            targetObserve (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (component n (N.agentAt site))))
          expect comparison.alternative (utility · who) -
            expect comparison.prescribed (utility · who) ≤ memberError n
  localComparisons : ∀ (weights : ℕ → ∀ p, PMF (Part p)) (targetSequence : ℕ →
      N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
              targetObserve (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool agent)).bind (component n agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ comparisonError : ℕ → ℝ, Tendsto comparisonError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who), N.agentAt site ∉ free →
          ∀ choice : N.Choice who site.1,
          let gain := fun law : PMF (N.Choice who site.1) =>
            let comparison := N.assessmentComparisonWith (N.truncatedRunner
                targetFuel) targetObserve (targetSequence n)
              who (site, ((targetSequence n).strategy who).withLaw site.1 law)
            expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who)
          gain (PMF.pure choice) ≤ comparisonError n ∨
            (∃ alternative : PMF (Part (pool (N.agentAt site))),
              gain (PMF.pure choice) ≤
                gain (alternative.bind (component n (N.agentAt site))) + comparisonError n) ∨
            ∃ mixture : PMF (M.AssessmentDeviation who),
              gain (PMF.pure choice) ≤
                expect mixture (fun deviation =>
                  let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                      sourceFuel) sourceObserve
                    (sourceSequence n) who deviation
                  expect sourceComparison.alternative (utility · who) -
                    expect sourceComparison.prescribed (utility · who)) + comparisonError n
  lawApproximation : ∀ (weights : ℕ → ∀ p, PMF (Part p)) (targetSequence : ℕ →
      N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel)
              targetObserve (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool agent)).bind (component n agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
        ∀ n outcome,
          |(((N.runBehavioral (targetSequence n).strategy targetFuel).map targetObserve)
              outcome).toReal -
            (((M.runBehavioral (sourceSequence n).strategy sourceFuel).map sourceObserve)
              outcome).toReal| ≤ lawError n

attribute [instance] PooledLimitCertificate.poolFinite PooledLimitCertificate.poolDecidable
  PooledLimitCertificate.partFinite PooledLimitCertificate.partNonempty

/-- A pooled limit certificate for a convergent source sequence of a
sequentially rational source assessment yields a target sequential equilibrium
with the source law. -/
theorem PooledLimitCertificate.exists_sequentialEquilibrium {Outcome : Type*}
    {sourceObserve : E.History → Outcome} {targetObserve : T.History → Outcome}
    {sourceFuel targetFuel : Nat} {targetBounded : T.BoundedHorizon targetFuel}
    {targetRecall : N.DecisionRecall} {utility : Outcome → Player → ℝ}
    {sourceSequence : ℕ → M.BehavioralAssessment}
    (certificate : PooledLimitCertificate sourceObserve targetObserve sourceFuel targetFuel
      targetBounded targetRecall utility sourceSequence)
    (source : M.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
        source.truncatedContinuationContext site (fun history => utility (sourceObserve history)
            who) sourceFuel) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetRecall.decisionInformationAntichain
        (fun who site => target.truncatedContinuationContext site
          (fun history => utility (targetObserve history) who) targetFuel) ∧
      (N.runBehavioral target.strategy targetFuel).map targetObserve =
        (M.runBehavioral source.strategy sourceFuel).map sourceObserve := by
  obtain ⟨target, equilibrium, law, _⟩ :=
    exists_sequentialEquilibrium_limit_of_pooled_comparisons_of_lawError sourceObserve
      targetObserve sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
      sourceConverges sourceRational certificate.fallback certificate.pool certificate.component
      certificate.componentFull certificate.free certificate.freeSpanning
      certificate.memberRational certificate.localComparisons certificate.lawApproximation
  exact ⟨target, equilibrium, law⟩

end GameTheory.Protocol.InformationModel
