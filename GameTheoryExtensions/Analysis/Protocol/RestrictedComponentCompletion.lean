/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ComponentCompletion
import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension

/-! # Consistent completion with restricted choices at new sites

Retained sites keep a prescribed consistent assessment. Every other information
agent chooses among an embedded nonempty finite menu, with full-menu trembles.
The common limit retains the prescribed beliefs and is optimal among its
restricted local laws, including at histories created by unrestricted trembles.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability Filter ExecutionProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E T : ExecutionProtocol ι} {M : InformationModel E} {N : InformationModel T}
  [Finite T.History] [∀ i, DecidableEq (N.InfoState i)]
  (restriction : M.ActionRestriction N)

/-- One common fully mixed approximation of a restricted completion. Every
local law is a tremble of an allowed lottery, with the source lottery retained
at prescribed sites. -/
structure RestrictedExtensionApproximation
    (reference target : N.BehavioralAssessment)
    (antichain : N.DecisionInformationAntichain)
    {Allowed : (who : ι) → N.InfoState who → Type*}
    (allowed : ∀ who info, Allowed who info ↪ N.Choice who info) where
  sequence : ℕ → N.BehavioralAssessment
  index : ℕ → ℕ
  increasing : StrictMono index
  converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) target
  mixed : ∀ n, (sequence n).IsFullyMixed
  bayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (sequence n) antichain
  epsilon : ℕ → ℝ
  positive : ∀ n, 0 < epsilon n
  small : ∀ n, epsilon n < 1
  vanishes : Tendsto epsilon atTop (nhds 0)
  retained : ∀ n who (site : M.InformationSite who),
    ∃ law : PMF (M.Choice who site.1),
      (sequence n).strategy who (restriction.information who site.1) =
        mix (epsilon n) (positive n).le (small n).le
          (reference.strategy who (restriction.information who site.1))
          (law.map (restriction.choice who site.1))
  fresh : ∀ n who (site : N.InformationSite who), ¬ restriction.Retained who site.1 →
    ∃ law : PMF (Allowed who site.1),
      (sequence n).strategy who site.1 =
        mix (epsilon n) (positive n).le (small n).le (reference.strategy who site.1)
          (law.map (allowed who site.1))

/-- Complete new sites over prescribed local submenus while retaining the
source profile and beliefs. Consistency uses the full target menus. -/
theorem exists_consistent_restricted_extension_unclocked
    (source : M.BehavioralAssessment) (sourceAntichain : M.DecisionInformationAntichain)
    (sourceConsistent : source.IsSequentiallyConsistent sourceAntichain)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (certificate : T.WellFoundedHistories)
    (payoff : ι → T.History → ℝ)
    {Allowed : (who : ι) → N.InfoState who → Type*}
    [∀ who info, Finite (Allowed who info)] [∀ who info, Nonempty (Allowed who info)]
    (allowed : ∀ who info, Allowed who info ↪ N.Choice who info) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (∀ who (site : N.InformationSite who), ¬ restriction.Retained who site.1 →
        ∃ law : PMF (Allowed who site.1),
          target.strategy who site.1 = law.map (allowed who site.1) ∧
          ∀ alternative : PMF (Allowed who site.1),
            (target.continuationContext certificate site (payoff who)).value
                ((target.strategy who).withLaw site.1
                  (alternative.map (allowed who site.1))) ≤
              (target.continuationContext certificate site (payoff who)).value
                (target.strategy who)) ∧
      Nonempty (restriction.RestrictedExtensionApproximation reference target
        decisionRecall.decisionInformationAntichain allowed) := by
  classical
  let _ := Fintype.ofFinite T.History
  have _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  let _ := Fintype.ofFinite (Σ who, M.InformationSite who)
  obtain ⟨sourceSequence, sourceApproximates, sourceConverges⟩ := sourceConsistent
  let mass (n : ℕ) (entry : Σ who, M.InformationSite who) : ℝ :=
    (M.informationMass (sourceSequence n).strategy entry.1 entry.2).toReal
  have massPositive (n : ℕ) (entry : Σ who, M.InformationSite who) : 0 < mass n entry :=
    ENNReal.toReal_pos
      (M.informationMass_pos_of_fullSupport _ (sourceApproximates n).1 entry.1 entry.2).ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (M.informationMass_le_one _ entry.1 entry.2 (sourceAntichain entry.1 entry.2)))
  let reach (n : ℕ) : ℝ := ∏ entry, min (1 : ℝ) (mass n entry)
  have reachPositive (n : ℕ) : 0 < reach n :=
    Finset.prod_pos fun entry _ => lt_min zero_lt_one (massPositive n entry)
  have reachBound (n : ℕ) (entry : Σ who, M.InformationSite who) : reach n ≤ mass n entry := by
    have bound := Finset.prod_le_prod_of_subset_of_le_one₀
      (s := {entry}) (t := Finset.univ) (f := fun other => min (1 : ℝ) (mass n other))
      (Finset.subset_univ _) (fun other _ => (lt_min zero_lt_one (massPositive n other)).le)
      (fun other _ _ => min_le_left _ _)
    have single : reach n ≤ min (1 : ℝ) (mass n entry) := by
      simpa only [Finset.prod_singleton] using bound
    exact single.trans (min_le_right _ _)
  let epsilon := relativeTremble reach
  have positive := relativeTremble_pos reach reachPositive
  have small := relativeTremble_lt_one reach
  have vanishes := relativeTremble_tendsto reach reachPositive
  let fallback (who : ι) : N.Policy who := fun info =>
    ((reference.strategy who info).support_nonempty).choose
  let referenceLaws : Profile (N.agentForm fallback certificate).sig.mixed :=
    fun agent => reference.strategy agent.1 agent.2.1
  have playedFull (who : ι) (info : N.InfoState who) (played : info ∈ N.playedInformation who) :
      FullSupport (reference.strategy who info) := by
    unfold playedInformation at played
    obtain ⟨history, member, rfl⟩ := Finset.mem_image.mp played
    have running := (Finset.mem_filter.mp member).2
    by_cases active : T.active history.state who
    · obtain ⟨site, same⟩ := N.exists_informationSite_of_active who history running active
      rw [← same]
      exact referenceMixed who site
    · let _ := N.subsingleton_choice_of_not_active history.trace active
      intro choice
      obtain ⟨witness, supported⟩ :=
        (reference.strategy who (N.infoOf who history.trace)).support_nonempty
      simpa only [Subsingleton.elim witness choice] using supported
  have referenceFull (agent : N.InformationAgent N.playedInformation) :
      FullSupport (referenceLaws agent) :=
    playedFull agent.1 agent.2.1 agent.2.2
  let pinned (n : ℕ) : Profile (N.agentForm fallback certificate).sig.mixed := fun agent =>
    restriction.perturbProfile (sourceSequence n).strategy reference.strategy
      (epsilon n) (positive n).le (small n).le agent.1 agent.2.1
  have pinnedFull (n : ℕ) (agent : N.InformationAgent N.playedInformation) :
      FullSupport (pinned n agent) :=
    restriction.perturbProfile_fullSupport (sourceSequence n).strategy reference.strategy
      (epsilon n) (positive n) (small n).le agent.1 agent.2.1 (referenceFull agent)
  let Component (agent : N.InformationAgent N.playedInformation) := Allowed agent.1 agent.2.1
  let component (n : ℕ) (agent : N.InformationAgent N.playedInformation)
      (part : Component agent) : PMF ((N.agentForm fallback certificate).sig.Strategy agent) :=
    if restriction.Retained agent.1 agent.2.1 then pinned n agent else
      mix (epsilon n) (positive n).le (small n).le (referenceLaws agent)
        (PMF.pure (allowed agent.1 agent.2.1 part))
  have componentFull (n : ℕ) (agent : N.InformationAgent N.playedInformation)
      (part : Component agent) : FullSupport (component n agent part) := by
    dsimp only [component]
    split
    · exact pinnedFull n agent
    · intro choice
      exact mem_support_mix_left _ _ _ (positive n) (referenceFull agent choice)
  obtain ⟨weights, sequence, target, index, played, mixed, bayes,
      increasing, converges, consistent, _stepOptimal, limitFacts⟩ :=
    N.exists_consistent_component_completion decisionRecall fallback certificate payoff component
      componentFull
  have perturbs (n : ℕ) : restriction.PerturbsProfile (sourceSequence n).strategy
      reference.strategy (sequence n).strategy (epsilon n) (positive n).le (small n).le := by
    intro who site
    let agent := N.agentAt (restriction.site who site)
    have componentAt : component n agent = fun _ => pinned n agent := by
      funext part
      exact ite_eq_left (restriction.retained_site who site)
    have playedAt := congrFun (congrFun (played n) who) (restriction.information who site.1)
    have bindAt : (weights n agent).bind (component n agent) = pinned n agent := by
      rw [componentAt, PMF.bind_const]
    exact playedAt.trans
      ((N.agentBehavior_at N.playedInformation fallback _ agent).trans
        (bindAt.trans
          (restriction.perturbProfile_perturbs (sourceSequence n).strategy reference.strategy
            (epsilon n) (positive n).le (small n).le who site)))
  have sourceAlong : BehavioralAssessmentConvergesPointwise
      (fun n => sourceSequence (index n)) source :=
    ⟨fun who site => (sourceConverges.strategy who site).subseq increasing,
      fun who site => (sourceConverges.belief who site).subseq increasing⟩
  have extendsTarget : restriction.ExtendsProfile source.strategy target.strategy :=
    restriction.extendsProfile_of_perturbs_converges reference.strategy
      (fun n => sourceSequence (index n)) source (fun n => sequence (index n)) target
      sourceAlong converges
      (fun n => epsilon (index n)) (fun n => (positive (index n)).le)
      (fun n => (small (index n)).le) (vanishes.comp increasing.tendsto_atTop)
      (fun n => perturbs (index n))
  obtain ⟨bound, -, bounded⟩ := T.exists_pos_boundedHorizon
  let sourceCertificate : E.WellFoundedHistories :=
    (restriction.boundedHorizon bounded).wellFoundedHistories
  refine ⟨target, consistent, extendsTarget, ?_, ?_, ?_⟩
  · intro who site
    let steps := Fintype.card ι * bound
    let factor (n : ℕ) := (1 - epsilon n) ^ steps
    have factorPositive (n : ℕ) : 0 < factor n := pow_pos (sub_pos.mpr (small n)) _
    have factorBound (n : ℕ) : factor n ≤ 1 :=
      pow_le_one₀ (sub_pos.mpr (small n)).le (by linarith [positive n])
    have negligible : Tendsto (fun n => (1 - factor n) /
        (factor n * (M.informationMass (sourceSequence n).strategy who site).toReal)) atTop
          (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact div_nonneg (sub_nonneg.mpr (factorBound n))
          (mul_nonneg (factorPositive n).le ENNReal.toReal_nonneg)
      · intro n
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr (factorBound n))
          (mul_pos (factorPositive n) (reachPositive n))
          (mul_le_mul_of_nonneg_left (reachBound n ⟨who, site⟩) (factorPositive n).le)
      · exact relativeTremble_power_ratio_tendsto reach reachPositive steps
    have lower (n : ℕ) (final : T.History) : factor n *
        (((M.runBehavioralTerminalFrom sourceCertificate (sourceSequence n).strategy
          E.initHistory).map restriction.history) final).toReal ≤
          ((N.runBehavioralTerminalFrom certificate (sequence n).strategy
            T.initHistory) final).toReal := by
      rw [M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded sourceCertificate
          (restriction.boundedHorizon bounded),
        N.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
      exact restriction.perturbed_run_domination (sourceSequence n).strategy
        reference.strategy (sequence n).strategy (epsilon n) (positive n).le (small n).le
        (perturbs n) bound final
    have beliefs := restriction.retained_beliefs_converge_unclocked sourceCertificate
      certificate sourceSequence sequence sourceAntichain
      decisionRecall.decisionInformationAntichain
      (fun n => (sourceApproximates n).1) mixed (fun n => (sourceApproximates n).2) bayes
      who site factor factorPositive factorBound lower negligible (source.belief who site)
      (sourceConverges.belief who site)
    exact (converges.belief who (restriction.site who site)).unique
      (beliefs.subseq increasing)
  · intro who site newSite
    let limitComponent : Component (N.agentAt site) → PMF (N.Choice who site.1) :=
      fun part => PMF.pure (allowed who site.1 part)
    have componentConverges (part : Component (N.agentAt site)) :
        PMFConvergesPointwise (fun n => component n (N.agentAt site) part)
          (limitComponent part) := by
      simp only [component, show ¬ restriction.Retained (N.agentAt site).1
        (N.agentAt site).2.1 from newSite, ↓reduceIte]
      exact pmfConvergesPointwise_mix_zero epsilon (fun n => (positive n).le)
        (fun n => (small n).le) vanishes _ _
    obtain ⟨⟨law, mixture⟩, optimal⟩ := limitFacts who site limitComponent componentConverges
    refine ⟨law, ?_, fun alternative => ?_⟩
    · simpa only [limitComponent, PMF.map, Function.comp_def] using mixture
    · simpa only [limitComponent, PMF.map, Function.comp_def] using optimal alternative
  · refine ⟨{
      sequence := sequence
      index := index
      increasing := increasing
      converges := converges
      mixed := mixed
      bayes := bayes
      epsilon := epsilon
      positive := positive
      small := small
      vanishes := vanishes
      retained := fun n who site => ⟨(sourceSequence n).strategy who site.1, perturbs n who site⟩
      fresh := ?_ }⟩
    intro n who site fresh
    let agent := N.agentAt site
    refine ⟨weights n agent, ?_⟩
    calc
      (sequence n).strategy who site.1 = (weights n agent).bind (component n agent) :=
        (congrFun (congrFun (played n) who) site.1).trans
          (N.agentBehavior_at N.playedInformation fallback _ agent)
      _ = ((weights n agent).map (allowed who site.1)).bind
          (fun choice => mix (epsilon n) (positive n).le (small n).le
            (reference.strategy who site.1) (PMF.pure choice)) := by
        rw [PMF.bind_map]
        apply congrArg ((weights n agent).bind)
        funext part
        exact ite_eq_right fresh
      _ = _ := bind_mix_pure _ _ _ _ _

end GameTheory.Protocol.InformationModel.ActionRestriction
