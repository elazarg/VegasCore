/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.AgentCompletion
import GameTheory.Analysis.Protocol.SequentialOneShot

/-! # Consistent rational completion outside prescribed information sites

Free agents receive optimal single-site laws, while prescribed agents retain
their specified strategy limit. Completing all sites of a free player yields
rationality against every whole continuation policy. If initialized reference play only visits
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


/-- Complete all decision sites of each free player rationally against whole
continuation policies, retaining every other player's prescribed decision laws.
One common consistency sequence supplies the free players' coherent beliefs;
no optimality is asserted for players whose strategy is prescribed. -/
private theorem consistent_player_completion_of_pinned_sequence
    (decisionRecall : M.DecisionRecall)
    (fallback : ∀ who, M.Policy who) (certificate : E.WellFoundedHistories)
    (payoff : Player → E.History → ℝ) (free : Finset Player)
    (pinned : ℕ → Profile (M.agentForm fallback certificate).sig.mixed)
    (reference : Profile (M.agentForm fallback certificate).sig.mixed)
    (pinnedFull : ∀ n agent, agent.1 ∉ free → FullSupport (pinned n agent))
    (referenceFull : ∀ agent, FullSupport (reference agent))
    (epsilon : ℕ → ℝ) (positive : ∀ n, 0 < epsilon n) (small : ∀ n, epsilon n < 1)
    (vanishes : Tendsto epsilon atTop (nhds 0))
    (prescribed : ∀ who, M.BehavioralPolicy who)
    (pinnedConverges : ∀ who (site : M.InformationSite who), who ∉ free →
      PMFConvergesPointwise (fun n => pinned n (M.agentAt site)) (prescribed who site.1)) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain ∧
      (∀ who (site : M.InformationSite who), who ∉ free →
        assessment.strategy who site.1 = prescribed who site.1) ∧
      (∀ who ∈ free, ∀ site : M.InformationSite who,
        assessment.IsSequentiallyRationalAt site
          (assessment.continuationContext certificate site (payoff who))) ∧
      ∃ (sequence : ℕ → M.BehavioralAssessment) (index : ℕ → ℕ),
        (∀ n, (sequence n).IsFullyMixed) ∧
        (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
          decisionRecall.decisionInformationAntichain) ∧
        StrictMono index ∧
        BehavioralAssessmentConvergesPointwise sequence assessment ∧
        ∀ n who (site : M.InformationSite who), who ∉ free →
          (sequence n).strategy who site.1 = pinned (index n) (M.agentAt site) := by
  classical
  let freeAgents : Finset (M.InformationAgent M.playedInformation) :=
    Finset.univ.filter fun agent => agent.1 ∈ free
  have freeAt (who : Player) (site : M.InformationSite who) :
      M.agentAt site ∈ freeAgents ↔ who ∈ free := by
    simp [freeAgents, agentAt]
  obtain ⟨_residual, sequence, assessment, index, played, mixed, bayes,
      increasing, converges, consistent, freeOptimal⟩ :=
    M.exists_consistent_free_agent_completion decisionRecall fallback certificate payoff
      freeAgents pinned reference (by simpa [freeAgents] using pinnedFull)
        referenceFull epsilon positive small vanishes
  refine ⟨assessment, consistent, ?_, ?_, ?_⟩
  · intro who site kept
    apply (converges.strategy who site).unique
    have same : (fun n => (sequence (index n)).strategy who site.1) =
        fun n => pinned (index n) (M.agentAt site) := by
      funext n
      rw [played]
      exact (M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)).trans
        (ite_eq_right (mt (freeAt who site).mp kept))
    rw [same]
    exact (pinnedConverges who site kept).subseq increasing
  · intro who member site
    apply (Context.isLocallyOptimal_iff_of_integrable
      (payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)).mpr
    intro alternative _
    exact consistent.continuation_value_le_of_locallyOptimal M decisionRecall
      (fun player _ _ => player ∈ free) payoff certificate
      (fun player decision law allowed =>
        freeOptimal player decision ((freeAt player decision).mpr allowed) law)
      who site alternative (fun _ => member)
  · refine ⟨(fun n => sequence (index n)), index,
      (fun n => mixed (index n)), (fun n => bayes (index n)), increasing, converges, ?_⟩
    intro n who site kept
    rw [played]
    exact (M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)).trans
      (ite_eq_right (mt (freeAt who site).mp kept))


omit [Fintype E.History] [∀ who, DecidableEq (M.InfoState who)] in
/-- In a finite decision-recall protocol, any fixed opponent profile admits a
consistent completion that makes every free player rational against arbitrary
whole continuation policies at every legal information site. The opponents'
decision laws are retained, without claiming their optimality. -/
theorem exists_consistent_player_completion [Finite E.History]
    (decisionRecall : M.DecisionRecall)
    (fallback : ∀ who, M.Policy who) (certificate : E.WellFoundedHistories)
    (payoff : Player → E.History → ℝ) (free : Finset Player)
    (prescribed : ∀ who, M.BehavioralPolicy who) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain ∧
      (∀ who (site : M.InformationSite who), who ∉ free →
        assessment.strategy who site.1 = prescribed who site.1) ∧
      ∀ who ∈ free, ∀ site : M.InformationSite who,
        assessment.IsSequentiallyRationalAt site
          (assessment.continuationContext certificate site (payoff who)) := by
  classical
  let _ := Fintype.ofFinite E.History
  let _ (agent : M.InformationAgent M.playedInformation) :
      Fintype ((M.agentForm fallback certificate).sig.Strategy agent) :=
    @Fintype.ofFinite _ (M.finite_choice_of_played agent.2.2)
  have _ (agent : M.InformationAgent M.playedInformation) :
      Nonempty ((M.agentForm fallback certificate).sig.Strategy agent) :=
    M.nonempty_choice_of_played agent.2.2
  let reference : Profile (M.agentForm fallback certificate).sig.mixed :=
    fun _ => PMF.uniformOfFintype _
  let epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have small (n : ℕ) : epsilon n < 1 := by
    dsimp [epsilon]
    rw [div_lt_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Tendsto epsilon atTop (nhds 0) := by
    have limit := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert limit using 1
    funext n
    simp [epsilon, Nat.cast_add]
    ring
  let pinned : ℕ → Profile (M.agentForm fallback certificate).sig.mixed :=
    fun n agent => mix (epsilon n) (positive n).le (small n).le (reference agent)
      (prescribed agent.1 agent.2.1)
  obtain ⟨assessment, consistent, agrees, rational, _witness⟩ :=
    consistent_player_completion_of_pinned_sequence M decisionRecall fallback certificate
    payoff free pinned reference
    (fun n agent _ choice => mem_support_mix_left _ _ _ (positive n)
      (PMF.mem_support_uniformOfFintype choice))
    (fun _ choice => PMF.mem_support_uniformOfFintype choice)
    epsilon positive small vanishes prescribed
    (fun who site _ => pmfConvergesPointwise_mix_zero epsilon (fun n => (positive n).le)
      (fun n => (small n).le) vanishes (reference (M.agentAt site)) (prescribed who site.1))
  exact ⟨assessment, consistent, agrees, rational⟩


omit [Fintype E.History] [∀ who, DecidableEq (M.InfoState who)] in
/-- When prescribed decision laws have full support, consistent whole-player
completion retains those laws at every approximant as well as at the limit.
The same sequence supplies Bayes beliefs and the free players' rationality. -/
theorem exists_consistent_full_support_player_completion [Finite E.History]
    (decisionRecall : M.DecisionRecall)
    (fallback : ∀ who, M.Policy who) (certificate : E.WellFoundedHistories)
    (payoff : Player → E.History → ℝ) (free : Finset Player)
    (prescribed : ∀ who, M.BehavioralPolicy who)
    (prescribedFull : ∀ who (site : M.InformationSite who), who ∉ free →
      FullSupport (prescribed who site.1)) :
    ∃ (sequence : ℕ → M.BehavioralAssessment) (assessment : M.BehavioralAssessment),
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
        decisionRecall.decisionInformationAntichain) ∧
      BehavioralAssessmentConvergesPointwise sequence assessment ∧
      (∀ n who (site : M.InformationSite who), who ∉ free →
        (sequence n).strategy who site.1 = prescribed who site.1) ∧
      assessment.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain ∧
      (∀ who (site : M.InformationSite who), who ∉ free →
        assessment.strategy who site.1 = prescribed who site.1) ∧
      ∀ who ∈ free, ∀ site : M.InformationSite who,
        assessment.IsSequentiallyRationalAt site
          (assessment.continuationContext certificate site (payoff who)) := by
  classical
  let _ := Fintype.ofFinite E.History
  let _ (agent : M.InformationAgent M.playedInformation) :
      Fintype ((M.agentForm fallback certificate).sig.Strategy agent) :=
    @Fintype.ofFinite _ (M.finite_choice_of_played agent.2.2)
  have _ (agent : M.InformationAgent M.playedInformation) :
      Nonempty ((M.agentForm fallback certificate).sig.Strategy agent) :=
    M.nonempty_choice_of_played agent.2.2
  let reference : Profile (M.agentForm fallback certificate).sig.mixed :=
    fun _ => PMF.uniformOfFintype _
  let epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have small (n : ℕ) : epsilon n < 1 := by
    dsimp [epsilon]
    rw [div_lt_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Tendsto epsilon atTop (nhds 0) := by
    have limit := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert limit using 1
    funext n
    simp [epsilon, Nat.cast_add]
    ring
  let pinned : ℕ → Profile (M.agentForm fallback certificate).sig.mixed :=
    fun _ agent => if M.IsDecisionInfo agent.1 agent.2.1 then
      prescribed agent.1 agent.2.1 else reference agent
  have pinnedFull (n : ℕ) (agent : M.InformationAgent M.playedInformation)
      (fixed : agent.1 ∉ free) : FullSupport (pinned n agent) := by
    by_cases decision : M.IsDecisionInfo agent.1 agent.2.1
    · simpa only [pinned, ite_eq_left decision] using
        prescribedFull agent.1 ⟨agent.2.1, decision⟩ fixed
    · simpa only [pinned, ite_eq_right decision, reference, FullSupport] using
        (fun choice => PMF.mem_support_uniformOfFintype choice)
  obtain ⟨assessment, consistent, agrees, rational, sequence, index,
      mixed, bayes, _increasing, converges, kept⟩ :=
    consistent_player_completion_of_pinned_sequence M decisionRecall fallback certificate
      payoff free pinned reference
      pinnedFull
      (fun _ choice => PMF.mem_support_uniformOfFintype choice)
      epsilon positive small vanishes prescribed
      (fun who site _ => by
        simpa only [pinned, agentAt, ite_eq_left site.2] using
          pmfConvergesPointwise_const (prescribed who site.1))
  refine ⟨sequence, assessment, mixed, bayes, converges, ?_, consistent, agrees, rational⟩
  intro n who site fixed
  simpa only [pinned, agentAt, ite_eq_left site.2] using kept n who site fixed

end GameTheory.Protocol.InformationModel
