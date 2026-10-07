/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.AgentCompletion
import GameTheory.Analysis.LocalChoiceFixedPoint
import GameTheoryExtensions.Analysis.Protocol.PassageBayes
import GameTheory.Math.Probability.Bounds

/-! # Consistent completion over component laws

Each agent of the agent normal form plays a mixture of finitely many fully
supported component laws, which may vary along a sequence; finite Nash
existence in the induced game over component weights chooses all weights
together. A single component is a prescribed law. A pure choice trembled toward
a fixed reference, one component per choice, is a free agent. In between, an
agent may be confined to mixtures of a few laws, for instance of waiting and of
acting with a prescribed law, each with its own trembles.

Agents may be pooled: the members of a pool mix their own components with one
common weight vector, and the completion makes the pool's weights optimal for
the sum of its members' conditional gains (`exists_pooled_bestResponses`,
`exists_consistent_pooled_completion`). Pooling agents that differ only in
private information makes a move whose law is chosen by the pool uninformative
about that information, as babbling does for cheap talk; each member is then
optimal up to an error whenever some part is nearly best for every member
(`pooled_member_le_of_common_best`). Without pooling, at every index the
weights of each agent are optimal among its own component mixtures, stated for
the Bayes continuation value of the fully mixed assessment. Along one common
subsequence the assessments converge to a consistent limit. Wherever the
components of an agent converge, its limit law is a mixture of the limit
components, and it is optimal among such mixtures when the agent's gains along
the sequence vanish.

Primary references: R. Selten, “Reexamination of the Perfectness Concept for
Equilibrium Points in Extensive Games,” *International Journal of Game
Theory* 4 (1975); D. M. Kreps and R. Wilson, “Sequential Equilibria,”
*Econometrica* 50 (1982).
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : GameForm ι}

/-- Each player chooses one of its components, whose law is then played in `F`. -/
private abbrev componentGame {Component : ι → Type*}
    (component : ∀ who, Component who → PMF (F.sig.Strategy who)) : GameForm ι where
  sig := { Strategy := Component, Outcome := F.sig.Outcome }
  play choice := F.mixed.play fun who => component who (choice who)

omit [DecidableEq ι] in
private theorem componentGame_mixed_play {Component : ι → Type*}
    (component : ∀ who, Component who → PMF (F.sig.Strategy who))
    (weights : ∀ who, PMF (Component who)) :
    (componentGame component).mixed.play weights =
      F.mixed.play fun who => (weights who).bind (component who) := by
  change (independentProduct weights).bind
      (fun choice => (independentProduct fun who => component who (choice who)).bind F.play) =
    (independentProduct fun who => (weights who).bind (component who)).bind F.play
  rw [← PMF.bind_bind, independentProduct_bind]

private theorem bind_component_update {Component : ι → Type*}
    (component : ∀ who, Component who → PMF (F.sig.Strategy who))
    (weights : ∀ who, PMF (Component who)) (who : ι) (alternative : PMF (Component who)) :
    (fun player => (Profile.update (sig := (componentGame component).sig.mixed) weights who
        alternative player).bind (component player)) =
      Profile.update (sig := F.sig.mixed) (fun player => (weights player).bind (component player))
        who (alternative.bind (component who)) := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [Profile.update_same]
  · simp only [Profile.update_of_ne _ _ same]

omit [DecidableEq ι] in
/-- A player's payoff polynomial, averaged over point masses at its own
strategies, is its payoff at the averaged weights. -/
private theorem expect_payoff_point [∀ who, Fintype (F.sig.Strategy who)] [DecidableEq ι]
    (utility : F.sig.Outcome → ι → ℝ) (y : Profile F.sig.weights) (who : ι)
    (law : PMF (F.sig.Strategy who)) :
    expect law (fun choice => payoff F utility who
        (Profile.update y who fun other => ((PMF.pure choice) other).toReal)) =
      payoff F utility who (Profile.update y who fun other => (law other).toReal) := by
  classical
  rw [expect_eq_sum]
  simp only [payoff_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun profile _ => ?_
  simp only [PMF.pure_apply, ← mul_assoc, ← Finset.sum_mul]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_one, ENNReal.toReal_zero, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- **Pooled best component mixtures.** Players are grouped into pools, and all
members of a pool mix their own components with one common weight vector over
the pool's parts. A fixed point chooses the weights of all pools together so
that no common replacement of a pool's weights raises the sum, over its
members, of each member's own expected utility gain weighted by its
`importance`, each member deviating alone against the same play of everybody
else. The importance of a member may depend continuously on the weights of all
players, for instance as the inverse of the probability of reaching it, which
turns the sum into a sum of conditional gains. With one player per pool and
unit importance this is Nash existence among component mixtures. -/
theorem exists_pooled_bestResponses [Finite F.sig.Outcome]
    {Pool : Type*} [Finite Pool] [DecidableEq Pool] (pool : ι → Pool)
    {Part : Pool → Type*} [∀ p, Finite (Part p)] [∀ p, Nonempty (Part p)]
    (utility : F.sig.Outcome → ι → ℝ)
    (component : ∀ who, Part (pool who) → PMF (F.sig.Strategy who))
    (importance : (∀ who, Part (pool who) → ℝ) → ι → ℝ)
    (importanceContinuous : ∀ who, ContinuousOn (fun weights => importance weights who)
      {weights | ∀ player, weights player ∈ simplexWeights (Part (pool player))}) :
    ∃ weights : ∀ p, PMF (Part p), ∀ (alternative : ∀ p, PMF (Part p)) (p : Pool),
      ∑ who ∈ Finset.univ.filter (fun who => pool who = p),
        importance (fun player part => (weights (pool player) part).toReal) who *
        (expectedUtility utility who (F.mixed.play
            (Profile.update (sig := F.sig.mixed)
              (fun player => (weights (pool player)).bind (component player))
              who ((alternative (pool who)).bind (component who)))) -
          expectedUtility utility who
            (F.mixed.play fun player => (weights (pool player)).bind (component player))) ≤
        0 := by
  classical
  let _ : Fintype Pool := Fintype.ofFinite Pool
  let G := componentGame (F := F) (Component := fun who => Part (pool who)) component
  let _ (p : Pool) : Fintype (Part p) := Fintype.ofFinite _
  let _ (who : ι) : Fintype (G.sig.Strategy who) := Fintype.ofFinite (Part (pool who))
  have : Finite G.sig.Outcome := inferInstanceAs (Finite F.sig.Outcome)
  have integrable : G.HasIntegrableUtility utility :=
    G.hasIntegrableUtility_of_finiteOutcome utility
  let spread (x : ∀ p, Part p → ℝ) : Profile G.sig.weights := fun who => x (pool who)
  have spreadContinuous : Continuous spread :=
    continuous_pi fun who => continuous_apply (pool who)
  have spreadInside (x : Set.pi Set.univ fun p => simplexWeights (Part p)) :
      spread x.1 ∈ {weights : ∀ who, Part (pool who) → ℝ |
        ∀ player, weights player ∈ simplexWeights (Part (pool player))} :=
    fun player => x.2 (pool player) (Set.mem_univ _)
  let point (who : ι) (choice : Part (pool who)) : Part (pool who) → ℝ :=
    fun other => ((PMF.pure choice) other).toReal
  let score (x : Set.pi Set.univ fun p => simplexWeights (Part p)) (p : Pool) (choice : Part p) :
      ℝ :=
    ∑ who, if h : pool who = p then
      importance (spread x.1) who * payoff G utility who (Profile.update (spread x.1) who
        (point who (cast (congrArg Part h.symm) choice)))
    else 0
  have scoreContinuous (p : Pool) (choice : Part p) :
      Continuous fun x => score x p choice := by
    refine continuous_finsetSum _ fun who _ => ?_
    split
    · exact ((importanceContinuous who).comp_continuous
        (spreadContinuous.comp continuous_subtype_val) spreadInside).mul
        (((continuous_payoff who).comp (continuous_update_profile who _)).comp
          (spreadContinuous.comp continuous_subtype_val))
    · exact continuous_const
  obtain ⟨x, optimal⟩ := exists_localChoice_fixedPoint score scoreContinuous
  let weights (p : Pool) : PMF (Part p) := PMF.ofSimplex (x.property p (Set.mem_univ p))
  let laws : Profile G.sig.mixed := fun who => weights (pool who)
  have spreadLaws : spread x.1 = probs G.sig laws := by
    funext who
    exact (PMF.ofSimplex_toReal (x.property (pool who) (Set.mem_univ _))).symm
  have spreadWeights : spread x.1 = fun player part => (weights (pool player) part).toReal :=
    spreadLaws
  have member (who : ι) (p : Pool) (h : pool who = p) (alternative : ∀ p, PMF (Part p)) :
      expect (alternative p) (fun choice => importance (spread x.1) who *
          payoff G utility who
          (Profile.update (spread x.1) who (point who (cast (congrArg Part h.symm) choice)))) =
        importance (spread x.1) who * expectedUtility utility who (F.mixed.play
          (Profile.update (sig := F.sig.mixed)
            (fun player => (weights (pool player)).bind (component player))
            who ((alternative (pool who)).bind (component who)))) := by
    subst h
    simp only [cast_eq]
    rw [expect_const_mul, expect_payoff_point (F := G) utility (spread x.1) who
      (alternative (pool who)), spreadLaws, ← probs_update, payoff_probs integrable,
      componentGame_mixed_play, bind_component_update]
  have total (alternative : ∀ p, PMF (Part p)) (p : Pool) :
      expect (alternative p) (score x p) =
        ∑ who ∈ Finset.univ.filter (fun who => pool who = p),
          importance (spread x.1) who * expectedUtility utility who (F.mixed.play
            (Profile.update (sig := F.sig.mixed)
              (fun player => (weights (pool player)).bind (component player))
              who ((alternative (pool who)).bind (component who)))) := by
    rw [Finset.sum_filter, expect_eq_sum]
    simp only [score, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun who _ => ?_
    by_cases h : pool who = p
    · rw [← member who p h alternative, expect_eq_sum]
      simp only [h, ↓reduceDIte, ite_true]
    · simp [h]
  refine ⟨weights, fun alternative p => ?_⟩
  have compared := optimal p (alternative p)
  rw [total alternative p, show PMF.ofSimplex (x.property p (Set.mem_univ p)) = weights p from rfl,
    total weights p] at compared
  have same (who : ι) :
      Profile.update (sig := F.sig.mixed)
          (fun player => (weights (pool player)).bind (component player))
          who ((weights (pool who)).bind (component who)) =
        fun player => (weights (pool player)).bind (component player) := by
    funext player
    by_cases equal : player = who
    · subst player
      simp only [Profile.update_same]
    · simp only [Profile.update_of_ne _ _ equal]
  simp only [same] at compared
  rw [← spreadWeights]
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

/-- **Simultaneous best component mixtures.** Each player plays a mixture of
finitely many component laws. Finite Nash existence selects the weights of all
players together, each optimal among its own component mixtures against the
same play of the others. -/
theorem exists_component_bestResponses [Finite F.sig.Outcome]
    {Component : ι → Type*} [∀ who, Finite (Component who)]
    [∀ who, Nonempty (Component who)]
    (utility : F.sig.Outcome → ι → ℝ)
    (component : ∀ who, Component who → PMF (F.sig.Strategy who)) :
    ∃ weights : ∀ who, PMF (Component who), ∀ who (alternative : PMF (Component who)),
      expectedUtility utility who (F.mixed.play
          (Profile.update (sig := F.sig.mixed)
            (fun player => (weights player).bind (component player))
            who (alternative.bind (component who)))) ≤
        expectedUtility utility who
          (F.mixed.play fun player => (weights player).bind (component player)) := by
  classical
  obtain ⟨weights, pooled⟩ := exists_pooled_bestResponses (F := F) (Part := Component) id
    utility component (fun _ _ => 1) (fun _ => continuousOn_const)
  refine ⟨weights, fun who alternative => ?_⟩
  have single := pooled (Function.update weights who alternative) who
  rw [show Finset.univ.filter (fun player : ι => id player = who) = {who} by
    ext player; simp, Finset.sum_singleton] at single
  simp only [id, Function.update_self, one_mul] at single
  linarith

/-- **Pooled rationality is member rationality when members share a best
part.** Each member of a pool values the pool's parts, and the pool's current
mixture is optimal for the unweighted sum of the members' gains. If one part is
within `error` of the best for every member, then every member's gain from any
mixture is at most the pool's size times `error`. A cheap-talk move that every
type ranks the same way, such as acting at once rather than waiting when the
wait can only lose inclusion probability, is pooled at a loss of at most this
error for each type. -/
theorem pooled_member_le_of_common_best {Member Part : Type*} [Finite Part]
    (members : Finset Member) (value : Member → Part → ℝ) (current : PMF Part)
    (best : Part) (error : ℝ)
    (nearBest : ∀ member ∈ members, ∀ part, value member part ≤ value member best + error)
    (pooled : ∀ alternative : PMF Part,
      ∑ member ∈ members, (expect alternative (value member) - expect current (value member)) ≤
        0) :
    ∀ member ∈ members, ∀ alternative : PMF Part,
      expect alternative (value member) - expect current (value member) ≤
        members.card * error := by
  classical
  intro chosen present alternative
  have errorNonnegative : 0 ≤ error := by
    have := nearBest chosen present best
    linarith
  have currentBound (member : Member) (inside : member ∈ members) :
      expect current (value member) ≤ value member best + error :=
    expect_le_const current _ (payoffIntegrable_of_finite _ _) _ fun part _ =>
      nearBest member inside part
  have alternativeBound : expect alternative (value chosen) ≤ value chosen best + error :=
    expect_le_const alternative _ (payoffIntegrable_of_finite _ _) _ fun part _ =>
      nearBest chosen present part
  have atBest := pooled (PMF.pure best)
  simp only [expect_pure] at atBest
  rw [← Finset.add_sum_erase members _ present] at atBest
  have others : -(((members.erase chosen).card : ℝ) * error) ≤
      ∑ member ∈ members.erase chosen,
        (value member best - expect current (value member)) := by
    have constant : ((members.erase chosen).card : ℝ) * error =
        ∑ _member ∈ members.erase chosen, error := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [constant, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun member inside => ?_
    have := currentBound member (Finset.mem_of_mem_erase inside)
    linarith
  have card : ((members.erase chosen).card : ℝ) + 1 = members.card := by
    rw [Finset.card_erase_of_mem present]
    have : 1 ≤ members.card := Finset.card_pos.mpr ⟨chosen, present⟩
    push_cast [Nat.cast_sub this]
    ring
  nlinarith

/-- The components that recover `pinnedTremble`: a free player has one
component per choice, the choice trembled toward the reference; every
component of another player is its pinned law. -/
def pinnedTrembleComponent (free : Finset ι) (pinned reference : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) (who : ι)
    (choice : F.sig.Strategy who) : PMF (F.sig.Strategy who) :=
  if who ∈ free then mix epsilon nonnegative small (reference who) (PMF.pure choice)
  else pinned who

omit [Fintype ι] in
/-- Mixing the pinned-tremble components with residual weights is the pinned
tremble of the residual laws. -/
theorem bind_pinnedTrembleComponent (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) (who : ι) :
    (residual who).bind (pinnedTrembleComponent free pinned reference epsilon nonnegative small
        who) =
      pinnedTremble free pinned reference residual epsilon nonnegative small who := by
  change (residual who).bind (fun choice =>
    if who ∈ free then mix epsilon nonnegative small (reference who) (PMF.pure choice)
    else pinned who) = _
  by_cases active : who ∈ free
  · simp only [pinnedTremble, active, ↓reduceIte, bind_mix_pure]
  · simp only [pinnedTremble, active, ↓reduceIte, PMF.bind_const]

end GameTheory

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ExecutionProtocol ι}
  (M : InformationModel E) [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)]

omit [DecidableEq ι] [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)] in
/-- The expected passage indicator of a decision site is its information mass. -/
private theorem expect_passage {i : ι} (site : M.InformationSite i)
    (antichain : site.IsHistoryAntichain) (certificate : E.WellFoundedHistories)
    (strategy : ∀ player, M.BehavioralPolicy player) :
    expect (M.runBehavioralTerminalFrom certificate strategy E.initHistory)
        (fun final => if (site.ancestor? M final).isSome then (1 : ℝ) else 0) =
      (M.informationMass strategy i site).toReal := by
  classical
  have indicator := expect_indicator (M.runBehavioralTerminalFrom certificate strategy
    E.initHistory) {final | (site.ancestor? M final).isSome = true}
  rw [← site.terminal_ancestor_passage M antichain certificate strategy, PMF.map_comp]
  convert indicator using 2
  · funext final
    by_cases passes : (site.ancestor? M final).isSome = true <;> simp [passes]
  rw [PMF.map_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun final => ?_
  by_cases passes : (site.ancestor? M final).isSome = true
  · simp [Set.indicator, passes]
  · simp_all [Set.indicator]

open Classical in
/-- **Consistent pooled completion.** Every agent plays a mixture of its fully
supported components with the weights of its pool; the weights of all pools are
chosen together by `exists_pooled_bestResponses`, with each member weighed by
the inverse of its site's probability. The assembled assessments are fully
mixed and Bayes consistent; at every index no common replacement of a pool's
weights raises the sum of its members' gains in Bayes continuation value. One
common subsequence converges to a consistent assessment. Wherever the
components of a site converge, the limit law is a mixture of the limit
components, and it is optimal among such mixtures as soon as the site's
component-mixture gains are bounded along the sequence by errors that vanish. -/
theorem exists_consistent_pooled_completion (hrecall : M.DecisionRecall)
    (fallback : (i : ι) → M.Policy i) (certificate : E.WellFoundedHistories)
    (payoff : ι → E.History → ℝ)
    {Pool : Type*} [Finite Pool] [DecidableEq Pool]
    (pool : M.InformationAgent M.playedInformation → Pool)
    {Part : Pool → Type*} [∀ p, Finite (Part p)] [∀ p, Nonempty (Part p)]
    (component : ℕ → ∀ agent, Part (pool agent) →
      PMF ((M.agentForm fallback certificate).sig.Strategy agent))
    (componentFull : ∀ n agent part, FullSupport (component n agent part)) :
    ∃ (weights : ℕ → ∀ p, PMF (Part p))
      (sequence : ℕ → M.BehavioralAssessment) (limit : M.BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = M.agentBehavior M.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
        hrecall.decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent hrecall.decisionInformationAntichain ∧
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : M.IsDecisionInfo agent.1 agent.2.1 then
            ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value
                (((sequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (pool agent)).bind (component n agent))) -
              ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value ((sequence n).strategy agent.1)
          else 0) ≤ 0) ∧
      ∀ i (site : M.InformationSite i)
        (limitComponent : Part (pool (M.agentAt site)) → PMF (M.Choice i site.1)),
        (∀ part, PMFConvergesPointwise (fun n => component n (M.agentAt site) part)
          (limitComponent part)) →
        (∃ limitWeights : PMF (Part (pool (M.agentAt site))),
          limit.strategy i site.1 = limitWeights.bind limitComponent) ∧
        ∀ (error : ℕ → ℝ), Filter.Tendsto error Filter.atTop (nhds 0) →
          (∀ n (alternative : PMF (Part (pool (M.agentAt site)))),
            ((sequence n).continuationContext certificate site (payoff i)).value
                (((sequence n).strategy i).withLaw site.1
                  (alternative.bind (component n (M.agentAt site)))) ≤
              ((sequence n).continuationContext certificate site (payoff i)).value
                ((sequence n).strategy i) + error n) →
          ∀ alternative : PMF (Part (pool (M.agentAt site))),
            (limit.continuationContext certificate site (payoff i)).value
                ((limit.strategy i).withLaw site.1 (alternative.bind limitComponent)) ≤
              (limit.continuationContext certificate site (payoff i)).value
                (limit.strategy i) := by
  classical
  let F := M.agentForm fallback certificate
  have : Finite F.sig.Outcome := inferInstanceAs (Finite E.History)
  let _ (p : Pool) : Fintype (Part p) := Fintype.ofFinite _
  let antichain := hrecall.decisionInformationAntichain
  obtain ⟨horizon, -, bounded⟩ := E.exists_pos_boundedHorizon
  have realize (profile : Profile F.sig.mixed) : F.mixed.play profile =
      M.runBehavioralTerminalFrom certificate
        (M.agentBehavior M.playedInformation fallback profile) E.initHistory :=
    M.informationAgentForm_mixed_play M.playedInformation fallback certificate bounded
      hrecall.actsOnceWhereItMatters (M.coversInformationSites_playedInformation horizon) profile
  -- the passage indicator of every decision agent
  let passage (final : E.History) (agent : M.InformationAgent M.playedInformation) : ℝ :=
    if decision : M.IsDecisionInfo agent.1 agent.2.1 then
      if (InformationSite.ancestor? M (⟨agent.2.1, decision⟩ : M.InformationSite agent.1)
          final).isSome then 1
      else 0
    else 0
  -- the reach of an agent as a polynomial in the part weights
  let reach (n : ℕ) (weights : ∀ agent, Part (pool agent) → ℝ)
      (agent : M.InformationAgent M.playedInformation) : ℝ :=
    GameTheory.payoff
      (componentGame (F := F) (Component := fun agent => Part (pool agent)) (component n))
      passage agent weights
  let mixtureOf (weights : ∀ agent, Part (pool agent) → ℝ)
      (inside : ∀ agent, weights agent ∈ simplexWeights (Part (pool agent)))
      (agent : M.InformationAgent M.playedInformation) : PMF (Part (pool agent)) :=
    PMF.ofSimplex (inside agent)
  have reachMass (n : ℕ) (weights : ∀ agent, Part (pool agent) → ℝ)
      (inside : ∀ agent, weights agent ∈ simplexWeights (Part (pool agent)))
      {i : ι} (site : M.InformationSite i) :
      reach n weights (M.agentAt site) =
        (M.informationMass (M.agentBehavior M.playedInformation fallback
          fun agent => (mixtureOf weights inside agent).bind (component n agent)) i
            site).toReal := by
    let G := componentGame (F := F) (Component := fun agent => Part (pool agent)) (component n)
    let _ (agent : M.InformationAgent M.playedInformation) : Fintype (G.sig.Strategy agent) :=
      Fintype.ofFinite (Part (pool agent))
    have : Finite G.sig.Outcome := inferInstanceAs (Finite E.History)
    have probsEq : probs G.sig (mixtureOf weights inside) = weights := by
      funext agent
      exact PMF.ofSimplex_toReal (inside agent)
    change GameTheory.payoff G passage (M.agentAt site) weights = _
    have key := payoff_probs (G.hasIntegrableUtility_of_finiteOutcome passage)
      (mixtureOf weights inside) (M.agentAt site)
    rw [probsEq] at key
    rw [key, componentGame_mixed_play, realize]
    change expect _ (fun final => passage final (M.agentAt site)) = _
    have decision : M.IsDecisionInfo i site.1 := site.2
    simp only [passage, decision, ↓reduceDIte]
    exact expect_passage M site (antichain i site) certificate _
  have mixtureFull (n : ℕ) (laws : ∀ agent, PMF (Part (pool agent))) :
      ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
        choice ∈ (M.agentBehavior M.playedInformation fallback
          (fun agent => (laws agent).bind (component n agent)) i site.1).support := by
    intro i site choice
    rw [M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)]
    obtain ⟨part, member⟩ := (laws (M.agentAt site)).support_nonempty
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨part, member, componentFull n _ part choice⟩
  let importance (n : ℕ) (weights : ∀ agent, Part (pool agent) → ℝ)
      (agent : M.InformationAgent M.playedInformation) : ℝ :=
    if M.IsDecisionInfo agent.1 agent.2.1 then (reach n weights agent)⁻¹ else 0
  have importanceContinuous (n : ℕ) (agent : M.InformationAgent M.playedInformation) :
      ContinuousOn (fun weights => importance n weights agent)
        {weights | ∀ player, weights player ∈ simplexWeights (Part (pool player))} := by
    let G := componentGame (F := F) (Component := fun agent => Part (pool agent)) (component n)
    let _ (agent : M.InformationAgent M.playedInformation) : Fintype (G.sig.Strategy agent) :=
      Fintype.ofFinite (Part (pool agent))
    by_cases decision : M.IsDecisionInfo agent.1 agent.2.1
    · simp only [importance, decision, ↓reduceIte]
      refine ContinuousOn.inv₀ (f := fun weights => reach n weights agent)
        (continuous_payoff (F := G) (utility := passage) agent).continuousOn ?_
      intro weights inside
      have positive := reachMass n weights inside (i := agent.1) ⟨agent.2.1, decision⟩
      change reach n weights agent = _ at positive
      rw [positive]
      refine (ENNReal.toReal_pos ?_ ?_).ne'
      · exact (M.informationMass_pos_of_fullSupport _ (mixtureFull n _) agent.1
          ⟨agent.2.1, decision⟩).ne'
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top
          (M.informationMass_le_one _ agent.1 _ (antichain agent.1 ⟨agent.2.1, decision⟩))
    · simp only [importance, decision, ↓reduceIte]
      exact continuousOn_const
  choose weights optimal using fun n =>
    exists_pooled_bestResponses (F := F) pool (M.agentUtility payoff) (component n)
      (importance n) (importanceContinuous n)
  let played (n : ℕ) : Profile F.sig.mixed := fun agent =>
    (weights n (pool agent)).bind (component n agent)
  let behavior (n : ℕ) := M.agentBehavior M.playedInformation fallback (played n)
  have full (n : ℕ) : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (behavior n i site.1).support :=
    mixtureFull n fun agent => weights n (pool agent)
  let sequence (n : ℕ) : M.BehavioralAssessment := M.bayesAssessment (behavior n) (full n) antichain
  have sequenceStrategy (n : ℕ) : (sequence n).strategy = behavior n :=
    M.bayesAssessment_strategy _ _ _
  have mixed (n : ℕ) : (sequence n).IsFullyMixed := by
    intro i site choice
    rw [sequenceStrategy]
    exact full n i site choice
  have bayes (n : ℕ) : BehavioralAssessment.IsBayesConsistent M (sequence n) antichain :=
    M.bayesAssessment_isBayesConsistent _ _ _
  obtain ⟨limit, index, increasing, converges⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight sequence
      (fun _ _ => uniformlyTight_of_finite _) (fun _ _ => uniformlyTight_of_finite _)
  have term (n : ℕ) (alternative : ∀ p, PMF (Part p))
      (agent : M.InformationAgent M.playedInformation) :
      importance n (fun player part => (weights n (pool player) part).toReal) agent *
        (expectedUtility (M.agentUtility payoff) agent
            (F.mixed.play (Profile.update (sig := F.sig.mixed) (played n) agent
              ((alternative (pool agent)).bind (component n agent)))) -
          expectedUtility (M.agentUtility payoff) agent (F.mixed.play (played n))) =
      if decision : M.IsDecisionInfo agent.1 agent.2.1 then
        ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
            (payoff agent.1)).value
            (((sequence n).strategy agent.1).withLaw agent.2.1
              ((alternative (pool agent)).bind (component n agent))) -
          ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
            (payoff agent.1)).value ((sequence n).strategy agent.1)
      else 0 := by
    by_cases decision : M.IsDecisionInfo agent.1 agent.2.1
    · let site : M.InformationSite agent.1 := ⟨agent.2.1, decision⟩
      have mass := reachMass n (fun player part => (weights n (pool player) part).toReal)
        (fun player => PMF.toReal_mem_simplexWeights _) site
      have lawsEq : (fun player => (mixtureOf (fun player part =>
            (weights n (pool player) part).toReal)
          (fun player => PMF.toReal_mem_simplexWeights _) player).bind (component n player)) =
          played n := by
        funext player
        simp only [mixtureOf, PMF.ofSimplex_toReal_weights, played]
      rw [lawsEq] at mass
      have gain := M.agentGain_eq_mass_mul hrecall fallback certificate payoff (played n)
        (full n) site ((alternative (pool agent)).bind (component n agent))
      have positive : 0 < (M.informationMass (behavior n) agent.1 site).toReal := by
        refine ENNReal.toReal_pos ?_ ?_
        · exact (M.informationMass_pos_of_fullSupport _ (full n) agent.1 site).ne'
        · exact ne_top_of_le_ne_top ENNReal.one_ne_top
            (M.informationMass_le_one _ agent.1 site (antichain agent.1 site))
      simp only [importance, decision, ↓reduceIte, ↓reduceDIte]
      change (reach n _ (M.agentAt site))⁻¹ * _ = _
      rw [mass]
      change _ * (expectedUtility (M.agentUtility payoff) (M.agentAt site) _ -
        expectedUtility (M.agentUtility payoff) (M.agentAt site) _) = _
      rw [gain, ← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]
      simp only [sequence, M.bayesAssessment_strategy]
      rfl
    · simp only [importance, decision, ↓reduceIte, ↓reduceDIte, zero_mul]
  refine ⟨weights, sequence, limit, index, sequenceStrategy, mixed, bayes, increasing, converges,
    converges.isSequentiallyConsistent antichain (fun n => mixed (index n))
      (fun n => bayes (index n)), fun n alternative p => ?_, ?_⟩
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun agent _ =>
      (term n alternative agent).symm)) ?_
    exact optimal n alternative p
  intro i site limitComponent componentConverges
  have strategyAt (n : ℕ) : (sequence n).strategy i site.1 =
      (weights n (pool (M.agentAt site))).bind (component n (M.agentAt site)) := by
    rw [sequenceStrategy]
    exact M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)
  constructor
  · obtain ⟨limitWeights, inner, innerIncreasing, weightsConverge⟩ :=
      exists_subseq_pmfConvergesPointwise
        (fun n => weights (index n) (pool (M.agentAt site)))
    refine ⟨limitWeights, ((converges.strategy i site).subseq innerIncreasing).unique ?_⟩
    have mixture := weightsConverge.bind
      (kernel := fun n => component (index (inner n)) (M.agentAt site))
      (fun part => (componentConverges part).subseq (increasing.comp innerIncreasing))
    simpa only [strategyAt] using mixture
  · intro error vanishes nearOptimal alternative
    let total : ℝ := ∑ history : E.History, |payoff i history|
    have totalBound (history : E.History) : |payoff i history| ≤ total :=
      Finset.single_le_sum (fun other _ => abs_nonneg (payoff i other)) (Finset.mem_univ history)
    have value (replacement : ℕ → M.BehavioralPolicy i) (target : M.BehavioralPolicy i)
        (hreplacement : ∀ decision : M.InformationSite i,
          PMFConvergesPointwise (fun n => replacement n decision.1) (target decision.1)) :=
      M.continuationContext_value_tendsto_of_bounded_terminal certificate
        (fun j decision => converges.strategy j decision) i site (converges.belief i site)
        hreplacement (payoff i) total ((abs_nonneg _).trans (totalBound E.initHistory))
        (fun final _ => totalBound final)
    have withLawLimit (laws : ℕ → PMF (M.Choice i site.1)) (target : PMF (M.Choice i site.1))
        (lawsConverge : PMFConvergesPointwise laws target) (decision : M.InformationSite i) :
        PMFConvergesPointwise
          (fun n => ((sequence (index n)).strategy i).withLaw site.1 (laws n) decision.1)
          ((limit.strategy i).withLaw site.1 target decision.1) := by
      by_cases hsame : decision = site
      · subst decision
        simpa only [BehavioralPolicy.withLaw_self] using lawsConverge
      · have different : decision.1 ≠ site.1 := fun equal => hsame (Subtype.ext equal)
        simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
          converges.strategy i decision
    have alternativeConverges : PMFConvergesPointwise
        (fun n => alternative.bind (component (index n) (M.agentAt site)))
        (alternative.bind limitComponent) :=
      (pmfConvergesPointwise_const alternative).bind
        (kernel := fun n => component (index n) (M.agentAt site))
        (fun part => (componentConverges part).subseq increasing)
    have upper := (value _ _ (converges.strategy i)).add
      (vanishes.comp increasing.tendsto_atTop)
    rw [add_zero] at upper
    exact le_of_tendsto_of_tendsto' (value _ _ (withLawLimit _ _ alternativeConverges)) upper
      fun n => nearOptimal (index n) alternative

/-- **Consistent completion over component laws.** Every agent plays a mixture
of its fully supported components; the weights of all agents are chosen
together by rational completion. The assembled assessments are fully mixed
and Bayes consistent, and at every index each agent's weights are optimal among
its own component mixtures for the Bayes continuation value. One common
subsequence converges to a consistent assessment. At every decision site whose
components converge, the limit law is a mixture of the limit components and is
optimal among such mixtures. This is the pooled completion with one agent per
pool. -/
theorem exists_consistent_component_completion (hrecall : M.DecisionRecall)
    (fallback : (i : ι) → M.Policy i) (certificate : E.WellFoundedHistories)
    (payoff : ι → E.History → ℝ)
    {Component : M.InformationAgent M.playedInformation → Type*}
    [∀ agent, Finite (Component agent)] [∀ agent, Nonempty (Component agent)]
    (component : ℕ → ∀ agent, Component agent →
      PMF ((M.agentForm fallback certificate).sig.Strategy agent))
    (componentFull : ∀ n agent part, FullSupport (component n agent part)) :
    ∃ (weights : ℕ → ∀ agent, PMF (Component agent))
      (sequence : ℕ → M.BehavioralAssessment) (limit : M.BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = M.agentBehavior M.playedInformation fallback
        fun agent => (weights n agent).bind (component n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
        hrecall.decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent hrecall.decisionInformationAntichain ∧
      (∀ n i (site : M.InformationSite i) (alternative : PMF (Component (M.agentAt site))),
        ((sequence n).continuationContext certificate site (payoff i)).value
            (((sequence n).strategy i).withLaw site.1
              (alternative.bind (component n (M.agentAt site)))) ≤
          ((sequence n).continuationContext certificate site (payoff i)).value
            ((sequence n).strategy i)) ∧
      ∀ i (site : M.InformationSite i)
        (limitComponent : Component (M.agentAt site) → PMF (M.Choice i site.1)),
        (∀ part, PMFConvergesPointwise (fun n => component n (M.agentAt site) part)
          (limitComponent part)) →
        (∃ limitWeights : PMF (Component (M.agentAt site)),
          limit.strategy i site.1 = limitWeights.bind limitComponent) ∧
        ∀ alternative : PMF (Component (M.agentAt site)),
          (limit.continuationContext certificate site (payoff i)).value
              ((limit.strategy i).withLaw site.1 (alternative.bind limitComponent)) ≤
            (limit.continuationContext certificate site (payoff i)).value
              (limit.strategy i) := by
  classical
  obtain ⟨weights, sequence, limit, index, played, mixed, bayes, increasing, converges,
      consistent, pooled, limitFacts⟩ :=
    M.exists_consistent_pooled_completion hrecall fallback certificate payoff (Part := Component)
      id component componentFull
  have stepOptimal (n : ℕ) (i : ι) (site : M.InformationSite i)
      (alternative : PMF (Component (M.agentAt site))) :
      ((sequence n).continuationContext certificate site (payoff i)).value
          (((sequence n).strategy i).withLaw site.1
            (alternative.bind (component n (M.agentAt site)))) ≤
        ((sequence n).continuationContext certificate site (payoff i)).value
          ((sequence n).strategy i) := by
    have single := pooled n (Function.update (weights n) (M.agentAt site) alternative)
      (M.agentAt site)
    rw [show Finset.univ.filter (fun agent => id agent = M.agentAt site) = {M.agentAt site} by
      ext agent; simp, Finset.sum_singleton,
      show Function.update (weights n) (M.agentAt site) alternative (id (M.agentAt site)) =
        alternative from Function.update_self ..] at single
    simp only [show M.IsDecisionInfo (M.agentAt site).1 (M.agentAt site).2.1 from site.2,
      ↓reduceDIte] at single
    exact sub_nonpos.mp single
  refine ⟨weights, sequence, limit, index, played, mixed, bayes, increasing, converges,
    consistent, stepOptimal, fun i site limitComponent componentConverges => ?_⟩
  obtain ⟨mixture, optimal⟩ := limitFacts i site limitComponent componentConverges
  exact ⟨mixture, optimal (fun _ => 0) tendsto_const_nhds fun n alternative => by
    rw [add_zero]
    exact stepOptimal n i site alternative⟩

end GameTheory.Protocol.InformationModel
