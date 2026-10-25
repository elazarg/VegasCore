/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

open Classical in
/-- **Sequential equilibrium with pooled component agents.** Every agent plays a
mixture of its fully supported components with the common weights of its pool,
the weights of all pools being chosen by pooled rational completion
(`exists_consistent_pooled_completion`): no common replacement of a pool's
weights raises the sum of its members' local continuation gains.
Pooling the agents that differ only in what a cheap-talk move should not reveal
makes those moves uninformative: all members move with one law.

The obligations may use these facts. Every site's component-mixture gains must
be at most a vanishing error (the member-rationality obligation), which is
automatic for an agent alone in its pool. At a free agent the limit components
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
      let comparison := N.assessmentComparisonWith (N.truncatedRunner targetFuel) targetObserve
        (sequence n) who (site, ((sequence n).strategy who).withLaw site.1 (PMF.pure choice))
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n + memberError n ∨
        ∃ mixture : PMF (M.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner sourceFuel)
                sourceObserve (sourceSequence n) who deviation
              expect sourceComparison.alternative (utility · who) -
                expect sourceComparison.prescribed (utility · who)) +
              (comparisonError n + memberError n) := by
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
    · left
      dsimp only at harmless ⊢
      linarith
    · left
      dsimp only at dominated ⊢
      have member := memberBound n who site alternative
      dsimp only at member
      linarith
    · right
      refine ⟨mixture, ?_⟩
      dsimp only at sourced ⊢
      linarith
  have result := sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve
    targetObserve sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational sequence (fun _ site => N.agentAt site ∉ free)
    (fun n => comparisonError n + memberError n)
    (by simpa only [zero_add] using errorVanishes.add memberVanishes)
    (fun n who site compared choice => choiceBound n who site compared choice)
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
