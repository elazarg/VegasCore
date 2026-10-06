/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.AgentCompletion
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit

/-! # Sequential equilibrium from comparisons at copied sites

The information agents of a target game are split in advance into copied and
free ones. Copied agents play prescribed laws, typically a compiled source
strategy with vanishing trembles, and must satisfy local comparisons with the
source game. Free agents tremble toward a fixed reference with a vanishing
weight and otherwise play residual laws chosen by finite Nash existence in the
agent normal form, so their optimality at the limit comes from rational
completion rather than from the source.

Since the residual laws are chosen by the completion, the comparisons and the
law approximation are required for every residual choice; their errors may
depend on it. One common subsequence then converges to a target sequential
equilibrium that keeps the prescribed limit at every copied agent and has the
source law.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite E.History] [Fintype T.History]
  [∀ who, DecidableEq (N.InfoState who)]

/-- **Sequential equilibrium with copied and free agents.** Copied agents (those
outside `free`) play `pinned`, which converges to `compiled`; free agents play
`epsilon`-trembles toward `reference` around residual laws chosen by rational
completion. If, for every choice of residual laws, local target gains at copied
sites are bounded by original-source gain mixtures up to a vanishing error, and
the target observation laws approach the perturbed source laws, then a target
sequential equilibrium exists that has the source law, agrees with `compiled` at
every copied site, and is the limit of one subsequence of the perturbed family.

The source assessment sequence and the comparisons are those of
`sequentialEquilibrium_of_copied_comparisons_limit_of_lawError`; with `free`
empty no residual law is used. -/
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
  let certificate := targetBounded.wellFoundedHistories
  obtain ⟨residual, sequence, target, index, played, mixed, bayes, increasing, converges,
      consistent, freeOptimal⟩ :=
    N.exists_consistent_free_agent_completion targetRecall fallback certificate
      (fun who history => utility (targetObserve history) who) free pinned reference pinnedFull
      referenceFull epsilon positive small vanishes
  obtain ⟨comparisonError, errorVanishes, comparisons⟩ :=
    localComparisons residual sequence played mixed bayes
  obtain ⟨lawError, lawErrorVanishes, approximation⟩ := lawApproximation residual
  have result := sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve
    targetObserve sourceFuel targetFuel targetBounded targetRecall utility source sourceSequence
    sourceConverges sourceRational sequence (fun _ site => N.agentAt site ∉ free)
    comparisonError errorVanishes comparisons lawError lawErrorVanishes
    (fun n outcome => by rw [played n]; exact approximation n outcome) target index increasing
    converges consistent (fun who site kept law => by
      have optimal := freeOptimal who site (not_not.mp kept) law
      rwa [target.continuationContext_eq_truncated_of_bounded certificate targetBounded] at optimal)
  have agrees (who : Player) (site : N.InformationSite who) (kept : N.agentAt site ∉ free) :
      target.strategy who site.1 = compiled who site.1 := by
    apply (converges.strategy who site).unique
    have same : (fun n => (sequence (index n)).strategy who site.1) =
        fun n => pinned (index n) (N.agentAt site) := by
      funext n
      rw [played]
      exact (N.agentBehavior_at N.playedInformation fallback _ (N.agentAt site)).trans
        (ite_eq_right kept)
    rw [same]
    exact (pinnedConverges who site kept).subseq increasing
  refine ⟨target, result.1, result.2, agrees, residual, index, increasing, fun who site => ?_⟩
  simpa only [played] using converges.strategy who site

end GameTheory.Protocol.InformationModel
