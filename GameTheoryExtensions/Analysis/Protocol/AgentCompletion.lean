/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ConstrainedNash
import GameTheoryExtensions.Analysis.Protocol.AgentForm
import GameTheoryExtensions.Analysis.Protocol.LocalDeviation
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Math.Probability.FinDist

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
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]

/-- Each positive tremble admits one fully mixed Bayes assessment whose free
agents' residual responses are optimal at every common-depth decision site.
The pinning and mandatory trembles are exact, not equilibrium assumptions. -/
theorem exists_pinned_agent_completion
    (sites : (who : Player) → Finset (M.InfoState who))
    (fallback : (who : Player) → M.Policy who) (horizon : Nat)
    (perfectRecall : M.PerfectRecall) (covered : M.CoversInformationSites sites horizon)
    (decisionCovered : ∀ who (site : M.InformationSite who), site.1 ∈ sites who)
    (utility : E.History → Player → ℝ) (free : Finset (M.InformationAgent sites))
    (pinned reference : (agent : M.InformationAgent sites) →
      FinDist (M.Choice agent.1 agent.2.1))
    (pinnedFull : ∀ agent, agent ∉ free → (pinned agent).FullSupport)
    (referenceFull : ∀ agent, (reference agent).FullSupport)
    (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon < 1) :
    ∃ (residual : (agent : M.InformationAgent sites) →
        FinDist (M.Choice agent.1 agent.2.1)) (assessment : M.BehavioralAssessment),
      assessment.strategy = M.agentBehavior sites fallback
        (pinnedTremble (F := M.informationAgentForm sites fallback horizon)
          free pinned reference residual epsilon positive.le small.le) ∧
      assessment.IsFullyMixed ∧
      BehavioralAssessment.IsBayesConsistent M assessment
        (M.decisionInformationAntichain_of_perfectRecall perfectRecall) ∧
      ∀ (who : Player) (site : M.InformationSite who) (present : site.1 ∈ sites who),
        (⟨who, ⟨site.1, present⟩⟩ : M.InformationAgent sites) ∈ free →
        ∀ depth fuel, InformationSite.CommonDepth M site depth → depth + fuel = horizon →
        ∀ alternative : FinDist (M.Choice who site.1),
          (assessment.continuationContext site (fun history => utility history who) fuel).value
            ((assessment.strategy who).withLaw site.1 alternative) ≤
          (assessment.continuationContext site (fun history => utility history who) fuel).value
            ((assessment.strategy who).withLaw site.1 (residual ⟨who, ⟨site.1, present⟩⟩)) := by
  classical
  let form := M.informationAgentForm sites fallback horizon
  let _ (agent : M.InformationAgent sites) : Finite (form.sig.Strategy agent) :=
    (referenceFull agent).finite
  let _ (agent : M.InformationAgent sites) : Nonempty (form.sig.Strategy agent) :=
    ⟨(reference agent).support_nonempty.choose⟩
  obtain ⟨residual, optimal⟩ := exists_pinned_tremble_bestResponses (F := form)
    (fun history agent => utility history agent.1) free pinned reference epsilon positive.le small
  let played := pinnedTremble (F := form) free pinned reference residual
    epsilon positive.le small.le
  let original := BehavioralAssessment.ofStrategy (M.agentBehavior sites fallback played)
  have playedFull : ∀ agent, (played agent).FullSupport :=
    pinnedTremble_fullSupport free pinned reference residual epsilon positive small.le
      pinnedFull (fun agent _ => referenceFull agent)
  have mixed : original.IsFullyMixed := by
    intro who site choice
    change choice ∈ (M.agentBehavior sites fallback played who site.1).support
    have law := M.agentBehavior_at sites fallback played ⟨who, ⟨site.1, decisionCovered who site⟩⟩
    rw [law]
    exact playedFull ⟨who, ⟨site.1, decisionCovered who site⟩⟩ choice
  let antichain := M.decisionInformationAntichain_of_perfectRecall perfectRecall
  let assessment := original.bayes mixed antichain
  have bayes : BehavioralAssessment.IsBayesConsistent M assessment antichain :=
    original.bayes_isBayesConsistent mixed antichain
  refine ⟨residual, assessment, rfl, mixed, bayes, ?_⟩
  intro who site present freeSite depth fuel sameDepth total alternative
  let agent : M.InformationAgent sites := ⟨who, ⟨site.1, present⟩⟩
  have bound := optimal agent freeSite alternative
  have realization (laws : Profile form.sig.mixed) :
      expectedUtility (fun history agent => utility history agent.1) agent
        (form.mixed.play laws) =
      (M.runBehavioral (M.agentBehavior sites fallback laws) horizon).expect
        (fun history => utility history who) := by
    change (form.mixed.play laws).expect (fun history => utility history who) = _
    rw [M.informationAgentForm_mixed_play sites fallback horizon
      (M.actsOnceWhereItMatters_of_perfectRecall perfectRecall) covered laws]
    rfl
  have first := realization (Profile.update (sig := form.sig.mixed) played agent alternative)
  have second := realization (Profile.update (sig := form.sig.mixed) played agent (residual agent))
  have nativeBound := first.symm.trans_le (bound.trans_eq second)
  rw [M.agentBehavior_update sites fallback played agent alternative,
    M.agentBehavior_update sites fallback played agent (residual agent)] at nativeBound
  apply (M.local_law_root_comparison_iff_context_comparison assessment perfectRecall
    who site depth fuel
    sameDepth (mixed.informationMass_pos who site)
    (bayes who site (mixed.informationMass_pos who site)) (fun history => utility history who)
    alternative (residual agent)).mp
  simpa only [total, assessment, BehavioralAssessment.bayes, original,
    BehavioralAssessment.ofStrategy, agent] using nativeBound

end GameTheory.Protocol.InformationModel
