/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.AgentCompletion

/-! # Consistent completion over component laws

Each agent of the agent normal form plays a mixture of finitely many fully
supported component laws, which may vary along a sequence; finite Nash
existence in the induced game over component weights chooses all weights
together. A single component is a prescribed law. A pure choice trembled toward
a fixed reference, one component per choice, is a free agent. In between, an
agent may be confined to mixtures of a few laws, for instance of waiting and of
acting with a prescribed law, each with its own trembles.

At every index the weights of each agent are optimal among its own component
mixtures, stated for the Bayes continuation value of the fully mixed
assessment. Along one common subsequence the assessments converge to a
consistent limit. Wherever the components of an agent converge, its limit law
is a mixture of the limit components and is optimal among such mixtures.

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
  let G := componentGame component
  let _ (who : ι) : Fintype (G.sig.Strategy who) := Fintype.ofFinite (Component who)
  have _ (who : ι) : Nonempty (G.sig.Strategy who) := inferInstanceAs (Nonempty (Component who))
  have : Finite G.sig.Outcome := inferInstanceAs (Finite F.sig.Outcome)
  have : Finite G.mixed.sig.Outcome := inferInstanceAs (Finite F.sig.Outcome)
  obtain ⟨weights, equilibrium⟩ := exists_isNash_mixed (F := G) utility
    (G.hasIntegrableUtility_of_finiteOutcome utility)
  refine ⟨weights, fun who alternative => ?_⟩
  have comparison := (isNash_iff (F := G.mixed) (weaklyPrefers := euPreference utility)
    weights).mp equilibrium who alternative
  replace comparison := (euPreference_iff _ _ _ _
    (G.mixed.hasIntegrableUtility_of_finiteOutcome utility who _)
    (G.mixed.hasIntegrableUtility_of_finiteOutcome utility who _)).mp comparison
  change expectedUtility utility who (G.mixed.play (Profile.update weights who alternative)) ≤
    expectedUtility utility who (G.mixed.play weights) at comparison
  rwa [componentGame_mixed_play, componentGame_mixed_play, bind_component_update] at comparison

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

/-- **Consistent completion over component laws.** Every agent plays a mixture
of its fully supported components; the weights of all agents are chosen
together by finite Nash existence. The assembled assessments are fully mixed
and Bayes consistent, and at every index each agent's weights are optimal among
its own component mixtures for the Bayes continuation value. One common
subsequence converges to a consistent assessment. At every decision site whose
components converge, the limit law is a mixture of the limit components and is
optimal among such mixtures. -/
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
  let F := M.agentForm fallback certificate
  have : Finite F.sig.Outcome := inferInstanceAs (Finite E.History)
  choose weights optimal using fun n =>
    exists_component_bestResponses (F := F) (M.agentUtility payoff) (component n)
  let played (n : ℕ) : Profile F.sig.mixed := fun agent =>
    (weights n agent).bind (component n agent)
  let behavior (n : ℕ) := M.agentBehavior M.playedInformation fallback (played n)
  have full (n : ℕ) : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (behavior n i site.1).support := by
    intro i site choice
    rw [show behavior n i site.1 = played n (M.agentAt site) from
      M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)]
    obtain ⟨part, member⟩ := (weights n (M.agentAt site)).support_nonempty
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨part, member, componentFull n _ part choice⟩
  let antichain := hrecall.decisionInformationAntichain
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
  have comparison (n : ℕ) {i : ι} (site : M.InformationSite i)
      (replacement : PMF (M.Choice i site.1)) :
      ((sequence n).continuationContext certificate site (payoff i)).value
          (((sequence n).strategy i).withLaw site.1 replacement) -
        ((sequence n).continuationContext certificate site (payoff i)).value
          ((sequence n).strategy i) =
      ((M.informationMass (behavior n) i site).toReal)⁻¹ *
        (expectedUtility (M.agentUtility payoff) (M.agentAt site)
            (F.mixed.play (Profile.update (played n) (M.agentAt site) replacement)) -
          expectedUtility (M.agentUtility payoff) (M.agentAt site) (F.mixed.play (played n))) := by
    have identity := M.agentGain_eq_mass_mul hrecall fallback certificate payoff (played n)
      (full n) site replacement
    have massPositive : 0 < (M.informationMass (behavior n) i site).toReal := by
      have positiveMass := M.informationMass_pos_of_fullSupport _ (mixed n) i site
      rw [sequenceStrategy] at positiveMass
      exact ENNReal.toReal_pos positiveMass.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
        (M.informationMass_le_one _ i site (antichain i site)))
    exact (eq_inv_mul_iff_mul_eq₀ massPositive.ne').mpr identity.symm
  have stepOptimal (n : ℕ) (i : ι) (site : M.InformationSite i)
      (alternative : PMF (Component (M.agentAt site))) :
      ((sequence n).continuationContext certificate site (payoff i)).value
          (((sequence n).strategy i).withLaw site.1
            (alternative.bind (component n (M.agentAt site)))) ≤
        ((sequence n).continuationContext certificate site (payoff i)).value
          ((sequence n).strategy i) := by
    have better : expectedUtility (M.agentUtility payoff) (M.agentAt site)
          (F.mixed.play (Profile.update (played n) (M.agentAt site)
            (alternative.bind (component n (M.agentAt site))))) ≤
        expectedUtility (M.agentUtility payoff) (M.agentAt site) (F.mixed.play (played n)) :=
      optimal n (M.agentAt site) alternative
    have identity := comparison n site (alternative.bind (component n (M.agentAt site)))
    have scaled := mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr (ENNReal.toReal_nonneg (a := M.informationMass (behavior n) i site)))
      (sub_nonpos.mpr better)
    linarith
  refine ⟨weights, sequence, limit, index, sequenceStrategy, mixed, bayes, increasing, converges,
    converges.isSequentiallyConsistent antichain (fun n => mixed (index n))
      (fun n => bayes (index n)), stepOptimal, ?_⟩
  intro i site limitComponent componentConverges
  have strategyAt (n : ℕ) : (sequence n).strategy i site.1 =
      (weights n (M.agentAt site)).bind (component n (M.agentAt site)) := by
    rw [sequenceStrategy]
    exact M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)
  constructor
  · obtain ⟨limitWeights, inner, innerIncreasing, weightsConverge⟩ :=
      exists_subseq_pmfConvergesPointwise (fun n => weights (index n) (M.agentAt site))
    refine ⟨limitWeights, ((converges.strategy i site).subseq innerIncreasing).unique ?_⟩
    have mixture := weightsConverge.bind
      (kernel := fun n => component (index (inner n)) (M.agentAt site))
      (fun part => (componentConverges part).subseq (increasing.comp innerIncreasing))
    simpa only [strategyAt] using mixture
  · intro alternative
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
    have upper := value _ _ (converges.strategy i)
    exact le_of_tendsto_of_tendsto' (value _ _ (withLawLimit _ _ alternativeConverges)) upper
      fun n => stepOptimal (index n) i site alternative

end GameTheory.Protocol.InformationModel
