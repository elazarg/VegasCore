/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.AgentCompletion

/-! # Consistent rational completion outside prescribed information sites

Free agents receive rational continuation play, while prescribed agents retain
their specified strategy limit. If initialized reference play only visits
prescribed decisions, the completion preserves its entire terminal history law.

The site classification and convergence of the prescribed sequence are explicit
premises. No rationality or source-belief transport at prescribed sites follows
from this result. In particular, a local risk flag alone need not identify the
information sites compatible with another game's prescribed play.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E)
  [Fintype E.History] [∀ who, DecidableEq (M.InfoState who)]

/-- Simultaneous rational completion preserves prescribed strategy limits and
the initialized terminal history law when all decisions on that play are
prescribed. The reference profile can contain unreachable decision sites. -/
theorem exists_consistent_prescribed_completion
    (decisionRecall : M.DecisionRecall)
    (fallback : ∀ who, M.Policy who) (certificate : E.WellFoundedHistories)
    (payoff : Player → E.History → ℝ)
    (free : Finset (M.InformationAgent M.playedInformation))
    (pinned : ℕ → Profile (M.agentForm fallback certificate).sig.mixed)
    (reference : Profile (M.agentForm fallback certificate).sig.mixed)
    (pinnedFull : ∀ n agent, agent ∉ free → FullSupport (pinned n agent))
    (referenceFull : ∀ agent, FullSupport (reference agent))
    (epsilon : ℕ → ℝ) (positive : ∀ n, 0 < epsilon n) (small : ∀ n, epsilon n < 1)
    (vanishes : Tendsto epsilon atTop (nhds 0))
    (prescribed : ∀ who, M.BehavioralPolicy who)
    (pinnedConverges : ∀ who (site : M.InformationSite who), M.agentAt site ∉ free →
      PMFConvergesPointwise (fun n => pinned n (M.agentAt site)) (prescribed who site.1))
    (protectedPlay : ∀ elapsed history,
      history ∈ (M.runBehavioralFrom prescribed elapsed E.initHistory).support →
      ¬ E.terminal history.state → ∀ who (site : M.InformationSite who),
        M.infoOf who history.trace = site.1 → M.agentAt site ∉ free) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain ∧
      (∀ who (site : M.InformationSite who), M.agentAt site ∉ free →
        assessment.strategy who site.1 = prescribed who site.1) ∧
      (∀ who (site : M.InformationSite who), M.agentAt site ∈ free →
        ∀ law : PMF (M.Choice who site.1),
          (assessment.continuationContext certificate site (payoff who)).value
              ((assessment.strategy who).withLaw site.1 law) ≤
            (assessment.continuationContext certificate site (payoff who)).value
              (assessment.strategy who)) ∧
      M.runBehavioralTerminalFrom certificate assessment.strategy E.initHistory =
        M.runBehavioralTerminalFrom certificate prescribed E.initHistory := by
  classical
  obtain ⟨_residual, sequence, assessment, index, played, _mixed, _bayes,
      increasing, converges, consistent, freeOptimal⟩ :=
    M.exists_consistent_free_agent_completion decisionRecall fallback certificate payoff free pinned
      reference pinnedFull referenceFull epsilon positive small vanishes
  have agrees (who : Player) (site : M.InformationSite who) (kept : M.agentAt site ∉ free) :
      assessment.strategy who site.1 = prescribed who site.1 := by
    apply (converges.strategy who site).unique
    have same : (fun n => (sequence (index n)).strategy who site.1) =
        fun n => pinned (index n) (M.agentAt site) := by
      funext n
      rw [played]
      exact (M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)).trans
        (ite_eq_right kept)
    rw [same]
    exact (pinnedConverges who site kept).subseq increasing
  refine ⟨assessment, consistent, agrees, freeOptimal, ?_⟩
  obtain ⟨bound, _positive, bounded⟩ := E.exists_pos_boundedHorizon
  rw [M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded,
    M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
  symm
  apply M.runBehavioralFrom_congr_on_support
  intro elapsed _ history reached running who
  by_cases active : E.active history.state who
  · obtain ⟨site, observed⟩ := M.exists_informationSite_of_active who history running active
    rw [← observed]
    exact (agrees who site (protectedPlay elapsed history reached running who site
      observed.symm)).symm
  · exact M.behavioral_eq_of_not_active (prescribed who) (assessment.strategy who)
      history.trace active

end GameTheory.Protocol.InformationModel
