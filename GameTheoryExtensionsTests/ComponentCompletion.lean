/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ComponentCompletion

/-! # Free-agent completion is a component completion

Consistent completion of free agents around prescribed ones is the component
completion whose free agents have one component per choice, trembled toward the
reference, and whose other agents have their pinned law as every component.
The free-agent statement is recovered verbatim.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ComponentCompletion

open GameTheory GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ExecutionProtocol ι}
  (M : InformationModel E) [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)]

/-- The consistent completion of free agents, derived from the component
completion with the pinned-tremble components. -/
theorem free_agent_completion_of_components (hrecall : M.DecisionRecall)
    (fallback : (i : ι) → M.Policy i) (certificate : E.WellFoundedHistories)
    (payoff : ι → E.History → ℝ) (free : Finset (M.InformationAgent M.playedInformation))
    (pinned : ℕ → Profile (M.agentForm fallback certificate).sig.mixed)
    (reference : Profile (M.agentForm fallback certificate).sig.mixed)
    (pinnedFull : ∀ n agent, agent ∉ free → FullSupport (pinned n agent))
    (referenceFull : ∀ agent, FullSupport (reference agent))
    (epsilon : ℕ → ℝ) (positive : ∀ n, 0 < epsilon n) (small : ∀ n, epsilon n < 1)
    (vanishes : Tendsto epsilon atTop (nhds 0)) :
    ∃ (residual : ℕ → Profile (M.agentForm fallback certificate).sig.mixed)
      (sequence : ℕ → M.BehavioralAssessment) (limit : M.BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = M.agentBehavior M.playedInformation fallback
        (pinnedTremble free (pinned n) reference (residual n) (epsilon n) (positive n).le
          (small n).le)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
        hrecall.decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent hrecall.decisionInformationAntichain ∧
      ∀ i (site : M.InformationSite i), M.agentAt site ∈ free →
        ∀ law : PMF (M.Choice i site.1),
          (limit.continuationContext certificate site (payoff i)).value
              ((limit.strategy i).withLaw site.1 law) ≤
            (limit.continuationContext certificate site (payoff i)).value
              (limit.strategy i) := by
  classical
  let F := M.agentForm fallback certificate
  let component (n : ℕ) := pinnedTrembleComponent (F := F) free (pinned n) reference (epsilon n)
    (positive n).le (small n).le
  have _ (agent : M.InformationAgent M.playedInformation) : Finite (F.sig.Strategy agent) :=
    M.finite_choice_of_played agent.2.2
  have _ (agent : M.InformationAgent M.playedInformation) : Nonempty (F.sig.Strategy agent) :=
    M.nonempty_choice_of_played agent.2.2
  have componentFull (n : ℕ) (agent : M.InformationAgent M.playedInformation)
      (choice : F.sig.Strategy agent) : FullSupport (component n agent choice) := by
    by_cases active : agent ∈ free
    · intro other
      simp only [component, pinnedTrembleComponent, active, ↓reduceIte]
      exact mem_support_mix_left _ _ _ (positive n) (referenceFull agent other)
    · simpa only [component, pinnedTrembleComponent, active, ↓reduceIte] using
        pinnedFull n agent active
  obtain ⟨residual, sequence, limit, index, played, mixed, bayes, increasing, converges,
      consistent, -, limitMixture⟩ :=
    M.exists_consistent_component_completion hrecall fallback certificate payoff
      (Component := fun agent => F.sig.Strategy agent) component componentFull
  refine ⟨residual, sequence, limit, index, fun n => ?_, mixed, bayes, increasing, converges,
    consistent, fun i site active law => ?_⟩
  · rw [played n]
    exact congrArg _ (funext fun agent => bind_pinnedTrembleComponent free (pinned n) reference
      (residual n) (epsilon n) (positive n).le (small n).le agent)
  · have optimal := (limitMixture i site PMF.pure fun choice => by
      simpa only [component, pinnedTrembleComponent, active, ↓reduceIte] using
        pmfConvergesPointwise_mix_zero epsilon (fun n => (positive n).le)
          (fun n => (small n).le) vanishes (reference (M.agentAt site)) (PMF.pure choice)).2 law
    rwa [PMF.bind_pure] at optimal

end GameTheoryExtensionsTests.ComponentCompletion
