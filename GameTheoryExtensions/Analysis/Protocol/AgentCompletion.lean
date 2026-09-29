/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ConstrainedNash
import GameTheoryExtensions.Analysis.Protocol.AgentForm
import GameTheoryExtensions.Analysis.Protocol.LocalDeviation
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Simultaneous Bayesian completion of free information agents

Finite Nash existence chooses all free local responses together. Exact agent
form realization and positive information-set reach then turn their ex ante
comparisons into actual Bayes continuation comparisons. Retained local laws
are prescribed independently; neither their optimality nor limiting source
beliefs are assumed or concluded here.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E)
  [∀ who, DecidableEq (M.InfoState who)]
  [∀ who (site : M.InformationSite who), Finite (M.InformationHistory who site.1)]

/-- Each positive tremble admits one fully mixed Bayes assessment whose free
agents' residual responses are optimal at every common-depth decision site.
The pinning and mandatory trembles are exact, not equilibrium assumptions.
Agent menus and reachable transitions must be finite. -/
theorem exists_pinned_agent_completion
    (sites : (who : Player) → Finset (M.InfoState who))
    [∀ agent : M.InformationAgent sites, Finite (M.Choice agent.1 agent.2.1)]
    (transitions : E.FiniteTransitions)
    (fallback : (who : Player) → M.Policy who) (horizon : Nat)
    (decisionRecall : M.DecisionRecall) (covered : M.CoversInformationSites sites horizon)
    (decisionCovered : ∀ who (site : M.InformationSite who), site.1 ∈ sites who)
    (utility : E.History → Player → ℝ) (free : Finset (M.InformationAgent sites))
    (pinned reference : (agent : M.InformationAgent sites) →
      PMF (M.Choice agent.1 agent.2.1))
    (pinnedFull : ∀ agent, agent ∉ free → FullSupport (pinned agent))
    (referenceFull : ∀ agent, FullSupport (reference agent))
    (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon < 1) :
    ∃ (residual : (agent : M.InformationAgent sites) →
        PMF (M.Choice agent.1 agent.2.1)) (assessment : M.BehavioralAssessment),
      assessment.strategy = M.agentBehavior sites fallback
        (pinnedTremble (F := M.informationAgentForm sites fallback horizon)
          free pinned reference residual epsilon positive.le small.le) ∧
      assessment.IsFullyMixed ∧
      BehavioralAssessment.IsBayesConsistent M assessment
        decisionRecall.decisionInformationAntichain ∧
      ∀ (who : Player) (site : M.InformationSite who) (present : site.1 ∈ sites who),
        (⟨who, ⟨site.1, present⟩⟩ : M.InformationAgent sites) ∈ free →
        ∀ depth fuel, InformationSite.CommonDepth M site depth → depth + fuel = horizon →
        ∀ alternative : PMF (M.Choice who site.1),
          (assessment.continuationContext site (fun history => utility history who) fuel).value
            ((assessment.strategy who).withLaw site.1 alternative) ≤
          (assessment.continuationContext site (fun history => utility history who) fuel).value
            ((assessment.strategy who).withLaw site.1 (residual ⟨who, ⟨site.1, present⟩⟩)) := by
  classical
  let form := M.informationAgentForm sites fallback horizon
  let _ (agent : M.InformationAgent sites) : Finite (form.sig.Strategy agent) :=
    inferInstanceAs (Finite (M.Choice agent.1 agent.2.1))
  have siteFinite (who : Player) (site : M.InformationSite who) :
      Finite (M.Choice who site.1) :=
    inferInstanceAs (Finite (M.Choice
      (⟨who, ⟨site.1, decisionCovered who site⟩⟩ : M.InformationAgent sites).1 site.1))
  have formIntegrable : form.HasIntegrableUtility (fun history agent => utility history agent.1) :=
    fun _ _ => payoffIntegrable_of_finite_support _ _
      (M.runFrom_support_finite transitions _ _ _)
  let _ (agent : M.InformationAgent sites) : Nonempty (form.sig.Strategy agent) :=
    ⟨(reference agent).support_nonempty.choose⟩
  obtain ⟨residual, optimal⟩ := exists_pinned_tremble_bestResponses (F := form)
    (fun history agent => utility history agent.1) formIntegrable free pinned reference epsilon
    positive.le small
  let played := pinnedTremble (F := form) free pinned reference residual
    epsilon positive.le small.le
  let original := BehavioralAssessment.ofStrategy (M.agentBehavior sites fallback played)
  have playedFull : ∀ agent, FullSupport (played agent) :=
    pinnedTremble_fullSupport free pinned reference residual epsilon positive small.le
      pinnedFull (fun agent _ => referenceFull agent)
  have mixed : original.IsFullyMixed := by
    intro who site choice
    change choice ∈ (M.agentBehavior sites fallback played who site.1).support
    have law := M.agentBehavior_at sites fallback played ⟨who, ⟨site.1, decisionCovered who site⟩⟩
    rw [law]
    exact playedFull ⟨who, ⟨site.1, decisionCovered who site⟩⟩ choice
  let antichain := decisionRecall.decisionInformationAntichain
  let assessment := InformationModel.bayesAssessment _ original.strategy mixed antichain
  have bayes : BehavioralAssessment.IsBayesConsistent M assessment antichain :=
    InformationModel.bayesAssessment_isBayesConsistent _ original.strategy mixed antichain
  refine ⟨residual, assessment, rfl, mixed, bayes, ?_⟩
  intro who site present freeSite depth fuel sameDepth total alternative
  let agent : M.InformationAgent sites := ⟨who, ⟨site.1, present⟩⟩
  have bound := optimal agent freeSite alternative
  have realization (laws : Profile form.sig.mixed) :
      expectedUtility (fun history agent => utility history agent.1) agent
        (form.mixed.play laws) =
      expect (M.runBehavioral (M.agentBehavior sites fallback laws) horizon)
        (fun history => utility history who) := by
    change expect (form.mixed.play laws) (fun history => utility history who) = _
    rw [M.informationAgentForm_mixed_play sites fallback horizon
      decisionRecall.actsOnceWhereItMatters covered laws]
    rfl
  have first := realization (Profile.update (sig := form.sig.mixed) played agent alternative)
  have second := realization (Profile.update (sig := form.sig.mixed) played agent (residual agent))
  have nativeBound := first.symm.trans_le (bound.trans_eq second)
  rw [M.agentBehavior_update sites fallback played agent alternative,
    M.agentBehavior_update sites fallback played agent (residual agent)] at nativeBound
  have positiveMass := M.informationMass_pos_of_fullSupport _ mixed who site
  have runIntegrable (profile : ∀ who, M.BehavioralPolicy who) (steps : Nat)
      (start : E.History) :
      PayoffIntegrable (M.runBehavioralFrom profile steps start)
        (fun history => utility history who) :=
    payoffIntegrable_of_finite_support _ _
      (runBehavioralFrom_support_finite transitions profile steps start)
  apply (M.local_law_root_comparison_iff_context_comparison assessment decisionRecall
    who site depth fuel sameDepth positiveMass (bayes who site positiveMass)
    (fun history => utility history who) alternative (residual agent)
    (runIntegrable _ _ _) (runIntegrable _ _ _) (runIntegrable _ _ _)
    (fun _ _ => runIntegrable _ _ _) (fun _ _ => runIntegrable _ _ _)
    (fun _ _ => runIntegrable _ _ _)).mp
  simpa only [total, assessment, InformationModel.bayesAssessment, original,
    BehavioralAssessment.ofStrategy, agent] using nativeBound

end GameTheory.Protocol.InformationModel
