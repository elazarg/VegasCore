/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.AgentCompletion
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity

/-! # Consistent limits of constrained information-agent completions

A vanishing mandatory tremble disappears from the free agents' chosen best
responses. Compactness then gives one consistent assessment, with locally
optimal behavior at every free information site. The actual approximating
sequence remains available to establish prescribed beliefs at retained sites.
Local optimality here compares one information-set law; whole-policy sequential
rationality still requires its separate perfect-recall bridge.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E}
  [∀ who, DecidableEq (M.InfoState who)]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]

omit [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)] in
/-- Conditional optimality of residual local responses survives a common
assessment limit when their mandatory tremble vanishes. -/
theorem BehavioralAssessmentConvergesPointwise.local_optimal_of_responses
    (referenceAssessment : M.BehavioralAssessment)
    (referenceMixed : referenceAssessment.IsFullyMixed)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    {who : Player} (site : M.InformationSite who)
    [Finite (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : Nat)
    (reference : FinDist (M.Choice who site.1))
    (responses : ℕ → FinDist (M.Choice who site.1))
    (epsilon : ℕ → ℝ) (positive : ∀ n, 0 < epsilon n)
    (small : ∀ n, epsilon n < 1) (vanishes : Tendsto epsilon atTop (nhds 0))
    (played : ∀ n, (sequence n).strategy who site.1 =
      FinDist.mix (epsilon n) (positive n).le (small n).le reference (responses n))
    (optimal : ∀ n alternative,
      ((sequence n).continuationContext site payoff fuel).value
        (((sequence n).strategy who).withLaw site.1 alternative) ≤
      ((sequence n).continuationContext site payoff fuel).value
        (((sequence n).strategy who).withLaw site.1 (responses n))) :
    ∀ alternative : FinDist (M.Choice who site.1),
      (assessment.continuationContext site payoff fuel).value
        ((assessment.strategy who).withLaw site.1 alternative) ≤
      (assessment.continuationContext site payoff fuel).value (assessment.strategy who) := by
  have responseLimit : FinDistConvergesPointwise responses (assessment.strategy who site.1) := by
    apply FinDistConvergesPointwise.of_mix_vanishing reference responses
      (assessment.strategy who site.1) epsilon (fun n => (positive n).le) small vanishes
    simpa only [← played] using converges.strategy who site
  intro alternative
  have leftLimit := converges.context_value referenceAssessment referenceMixed site payoff fuel
    (fun n => ((sequence n).strategy who).withLaw site.1 alternative)
    ((assessment.strategy who).withLaw site.1 alternative) (by
      intro decision
      by_cases same : decision = site
      · subst decision
        simpa only [BehavioralPolicy.withLaw_self] using
          finDistConvergesPointwise_const alternative
      · have different : decision.1 ≠ site.1 := fun equal => same (Subtype.ext equal)
        simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
          converges.strategy who decision)
  have rightLimit := converges.context_value referenceAssessment referenceMixed site payoff fuel
    (fun n => ((sequence n).strategy who).withLaw site.1 (responses n))
    (assessment.strategy who) (by
      intro decision
      by_cases same : decision = site
      · subst decision
        simpa only [BehavioralPolicy.withLaw_self] using responseLimit
      · have different : decision.1 ≠ site.1 := fun equal => same (Subtype.ext equal)
        simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
          converges.strategy who decision)
  exact le_of_tendsto_of_tendsto leftLimit rightLimit
    (Eventually.of_forall fun n => optimal n alternative)

/-- Simultaneously complete all free information sites, retaining the exact
prescribed local laws and a common consistency sequence. The pinned laws need
not converge here: their limit and retained beliefs can be identified from the
exposed sequence using game-specific restriction and contamination facts. -/
theorem exists_consistent_free_agent_completion
    (sites : (who : Player) → Finset (M.InfoState who))
    (fallback : (who : Player) → M.Policy who) (horizon : Nat)
    (perfectRecall : M.PerfectRecall) (covered : M.CoversInformationSites sites horizon)
    (decisionCovered : ∀ who (site : M.InformationSite who), site.1 ∈ sites who)
    (utility : E.History → Player → ℝ) (free : Finset (M.InformationAgent sites))
    (pinned : ℕ → (agent : M.InformationAgent sites) →
      FinDist (M.Choice agent.1 agent.2.1))
    (reference : (agent : M.InformationAgent sites) →
      FinDist (M.Choice agent.1 agent.2.1))
    (pinnedFull : ∀ n agent, agent ∉ free → (pinned n agent).FullSupport)
    (referenceFull : ∀ agent, (reference agent).FullSupport)
    (epsilon : ℕ → ℝ) (positive : ∀ n, 0 < epsilon n)
    (small : ∀ n, epsilon n < 1) (vanishes : Tendsto epsilon atTop (nhds 0)) :
    ∃ (residual : ℕ → (agent : M.InformationAgent sites) →
        FinDist (M.Choice agent.1 agent.2.1))
      (sequence : ℕ → M.BehavioralAssessment) (assessment : M.BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = M.agentBehavior sites fallback
        (pinnedTremble (F := M.informationAgentForm sites fallback horizon)
          free (pinned n) reference (residual n) (epsilon n)
            (positive n).le (small n).le)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
        (M.decisionInformationAntichain_of_perfectRecall perfectRecall)) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) assessment ∧
      assessment.IsSequentiallyConsistent
        (M.decisionInformationAntichain_of_perfectRecall perfectRecall) ∧
      ∀ (who : Player) (site : M.InformationSite who) (present : site.1 ∈ sites who),
        (⟨who, ⟨site.1, present⟩⟩ : M.InformationAgent sites) ∈ free →
        ∀ depth fuel, InformationSite.CommonDepth M site depth → depth + fuel = horizon →
        ∀ alternative : FinDist (M.Choice who site.1),
          (assessment.continuationContext site (fun history => utility history who) fuel).value
            ((assessment.strategy who).withLaw site.1 alternative) ≤
          (assessment.continuationContext site (fun history => utility history who) fuel).value
            (assessment.strategy who) := by
  classical
  let _ (who : Player) : Finite (M.InformationSite who) :=
    Finite.of_injective
      (fun site : M.InformationSite who =>
        (⟨site.1, decisionCovered who site⟩ : {info // info ∈ sites who}))
      (fun _ _ equal => Subtype.ext
        (congrArg (fun entry : {info // info ∈ sites who} => entry.1) equal))
  choose residual sequence played mixed bayes optimal using fun n =>
    M.exists_pinned_agent_completion sites fallback horizon perfectRecall covered
      decisionCovered utility free (pinned n) reference (pinnedFull n) referenceFull
      (epsilon n) (positive n) (small n)
  obtain ⟨assessment, index, increasing, converges, consistent⟩ :=
    BehavioralAssessment.exists_sequentiallyConsistent_subsequence
      (M.decisionInformationAntichain_of_perfectRecall perfectRecall) sequence mixed bayes
  refine ⟨residual, sequence, assessment, index, played, mixed, bayes,
    increasing, converges, consistent, ?_⟩
  intro who site present freeSite depth fuel sameDepth total
  let agent : M.InformationAgent sites := ⟨who, ⟨site.1, present⟩⟩
  have freeAgent : agent ∈ free := freeSite
  apply converges.local_optimal_of_responses (sequence 0) (mixed 0) site
    (fun history => utility history who) fuel (reference agent)
    (fun n => residual (index n) agent) (fun n => epsilon (index n))
    (fun n => positive (index n)) (fun n => small (index n))
    (vanishes.comp increasing.tendsto_atTop)
  · intro n
    rw [played]
    rw [M.agentBehavior_at sites fallback _ agent]
    simp only [pinnedTremble, ite_eq_left freeAgent]
  · intro n alternative
    exact optimal (index n) who site present freeSite depth fuel sameDepth total alternative

end GameTheory.Protocol.InformationModel
