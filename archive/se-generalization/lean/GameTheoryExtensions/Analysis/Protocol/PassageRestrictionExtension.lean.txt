/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.RestrictionExtension
import GameTheory.Analysis.Protocol.SubgameLocalization
import GameTheoryExtensions.Analysis.Protocol.AgentPayoffCompletion

/-! # Extension across an action restriction without a common decision depth

The library extends sequential equilibria across an action restriction when
every retained site of the larger protocol lies at a common decision depth.
The depth serves only to read the Bayes belief at a retained site off the
prefix law of that length, in
`GameTheory.Protocol.InformationModel.ActionRestriction.retained_beliefs_converge`.
This module reads it off terminal play instead: a
site history's belief is the probability that terminal play passes through it,
divided by the probability that terminal play passes through the site. The
embedding of histories preserves and reflects reachability, so passage through
a retained site corresponds exactly to passage through its embedding, and
terminal-law domination replaces prefix-law domination at the common depth.
The resulting extension theorems need no depth hypothesis.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

variable {α : Type*}

private theorem ratio_domination_bound (point mass changed total factor : ℝ)
    (massPositive : 0 < mass) (totalPositive : 0 < total)
    (pointNonnegative : 0 ≤ point) (pointWithin : point ≤ mass)
    (factorPositive : 0 < factor) (factorAtMostOne : factor ≤ 1)
    (pointLower : factor * point ≤ changed)
    (pointExcess : changed - factor * point ≤ 1 - factor)
    (massLower : factor * mass ≤ total)
    (massExcess : total - factor * mass ≤ 1 - factor) :
    |changed / total - point / mass| ≤ (1 - factor) / (factor * mass) := by
  have fractionNonnegative : 0 ≤ point / mass := div_nonneg pointNonnegative massPositive.le
  have fractionAtMostOne : point / mass ≤ 1 := (div_le_one massPositive).mpr pointWithin
  have excessNonnegative : 0 ≤ total - factor * mass := sub_nonneg.mpr massLower
  have missingNonnegative : 0 ≤ 1 - factor := sub_nonneg.mpr factorAtMostOne
  have scaledNonnegative := mul_nonneg fractionNonnegative excessNonnegative
  have scaledUpper : (point / mass) * (total - factor * mass) ≤ 1 - factor :=
    (mul_le_mul_of_nonneg_left massExcess fractionNonnegative).trans
      (mul_le_of_le_one_left missingNonnegative fractionAtMostOne)
  have numerator : |(changed - factor * point) -
      (point / mass) * (total - factor * mass)| ≤ 1 - factor := by
    apply abs_le.mpr
    constructor <;> linarith
  have difference : changed / total - point / mass =
      ((changed - factor * point) - (point / mass) * (total - factor * mass)) / total := by
    field_simp
    ring
  rw [difference, abs_div, abs_of_pos totalPositive]
  exact (div_le_div_of_nonneg_right numerator totalPositive.le).trans
    (div_le_div_of_nonneg_left missingNonnegative (mul_pos factorPositive massPositive)
      massLower)

/-- **Conditional domination on a sub-event.** Domination by a near-unit
source component bounds the error of the conditional probability of every part
of the conditioning event, not only of its points, by the missing mass divided
by the source mass of the event. -/
theorem conditional_domination_bound_of_subset (source target : PMF α) (event part : Set α)
    (inside : part ⊆ event)
    (sourcePositive : 0 < (source.toOuterMeasure event).toReal)
    (targetPositive : 0 < (target.toOuterMeasure event).toReal)
    (factor : ℝ) (positive : 0 < factor) (atMostOne : factor ≤ 1)
    (lower : ∀ a, factor * (source a).toReal ≤ (target a).toReal) :
    |(target.toOuterMeasure part).toReal / (target.toOuterMeasure event).toReal -
      (source.toOuterMeasure part).toReal / (source.toOuterMeasure event).toReal| ≤
        (1 - factor) / (factor * (source.toOuterMeasure event).toReal) :=
  ratio_domination_bound _ _ _ _ _ sourcePositive targetPositive ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (outerMeasure_ne_top source event)
      (MeasureTheory.measure_mono inside))
    positive atMostOne (probOf_domination source target factor lower part)
    (probOf_domination_excess source target factor lower part)
    (probOf_domination source target factor lower event)
    (probOf_domination_excess source target factor lower event)

/-- A vanishing relative loss transports the conditional probability of every
part of the conditioning event, without any lower bound on the limiting
probability of the event. -/
theorem conditional_domination_converges_of_subset (source target : ℕ → PMF α)
    (event part : Set α) (inside : part ⊆ event)
    (sourcePositive : ∀ n, 0 < ((source n).toOuterMeasure event).toReal)
    (targetPositive : ∀ n, 0 < ((target n).toOuterMeasure event).toReal)
    (factor : ℕ → ℝ) (positive : ∀ n, 0 < factor n) (atMostOne : ∀ n, factor n ≤ 1)
    (lower : ∀ n a, factor n * ((source n) a).toReal ≤ ((target n) a).toReal)
    (negligible : Tendsto (fun n =>
      (1 - factor n) / (factor n * ((source n).toOuterMeasure event).toReal)) atTop (nhds 0))
    (limit : ℝ)
    (converges : Tendsto (fun n => ((source n).toOuterMeasure part).toReal /
      ((source n).toOuterMeasure event).toReal) atTop (nhds limit)) :
    Tendsto (fun n => ((target n).toOuterMeasure part).toReal /
      ((target n).toOuterMeasure event).toReal) atTop (nhds limit) := by
  apply converges.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ negligible
  intro n
  simpa only [Real.dist_eq, abs_sub_comm] using
    conditional_domination_bound_of_subset (source n) (target n) event part inside
      (sourcePositive n) (targetPositive n) (factor n) (positive n) (atMostOne n) (lower n)

end GameTheory.Math.Probability

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type*} {E T : ExecutionProtocol ι}
  {M : InformationModel E} {N : InformationModel T}

/-- **Passage form of Bayes beliefs.** The Bayes belief in a site history is
the probability that terminal play passes through it, divided by the
probability that terminal play passes through the site. -/
theorem bayesBelief_apply_eq_passage [Fintype ι] (certificate : E.WellFoundedHistories)
    (strategy : (i : ι) → M.BehavioralPolicy i) (who : ι) (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain) (positive : 0 < M.informationMass strategy who site)
    (history : M.InformationHistory who site.1) :
    M.bayesBelief strategy who site antichain positive history =
      (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure
          {final | E.HistoryReaches history.1 final} /
        (M.runBehavioralTerminalFrom certificate strategy E.initHistory).toOuterMeasure
          {final | ∃ history, M.infoOf who history.trace = site.1 ∧
            E.HistoryReaches history final} := by
  rw [M.bayesBelief_apply, ← M.informationMass_eq_passage certificate strategy who site antichain,
    ← M.coneMass_eq_historyReachWeight certificate strategy history.1]
  rfl

private theorem bayes_belief_eq [Fintype ι] (assessment : M.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain)
    (positive : 0 < M.informationMass assessment.strategy who site)
    (bayes : BehavioralAssessment.IsBayesConsistentAt M assessment who site antichain positive) :
    assessment.belief who site = M.bayesBelief assessment.strategy who site antichain positive := by
  ext history
  rw [M.bayesBelief_apply]
  exact bayes history

namespace ActionRestriction

variable (restriction : M.ActionRestriction N)

/-- One legal step of the smaller protocol embeds as one step of the larger. -/
theorem reachesWithin_step {start : E.History} {joint : ∀ i, Option (E.Action i)}
    (isLegal : E.Legal start.state joint) {reached : E.State}
    (realized : reached ∈ (E.step start.state ⟨joint, isLegal⟩).support) :
    T.ReachesWithin 1 (restriction.history start)
      (restriction.history (start.extend isLegal realized)) := by
  classical
  let choices (who : ι) : M.Choice who (M.infoOf who start.trace) :=
    ⟨joint who, (M.menu_adequate who start.trace (joint who)).mpr
      (ExecutionProtocol.legalOption_of_legal isLegal who)⟩
  have source : start.extend isLegal realized ∈ (M.localStep start choices).support := by
    rw [localStep, dite_eq_right isLegal.1, PMF.mem_support_bindOnSupport_iff]
    exact ⟨reached, realized, by rw [PMF.support_pure]; rfl⟩
  have image : restriction.history (start.extend isLegal realized) ∈
      ((M.localStep start choices).map restriction.history).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨_, source, rfl⟩
  have running : ¬ T.terminal (restriction.history start).state :=
    fun stopped => isLegal.1 ((restriction.terminal start).mp stopped)
  rw [restriction.step start choices, localStep, dite_eq_right running,
    PMF.mem_support_bindOnSupport_iff] at image
  obtain ⟨next, step, landed⟩ := image
  rw [PMF.support_pure, Set.mem_singleton_iff] at landed
  rw [landed]
  exact .step _ _ step (.refl 0 _)

/-- The embedding of histories preserves bounded reachability. -/
theorem reachesWithin_history {fuel : ℕ} {start final : E.History}
    (reach : E.ReachesWithin fuel start final) :
    T.ReachesWithin fuel (restriction.history start) (restriction.history final) := by
  induction reach with
  | refl fuel history => exact .refl fuel _
  | step joint isLegal realized rest induction =>
      simpa only [Nat.add_comm] using (restriction.reachesWithin_step isLegal realized).trans
        induction

theorem historyReaches_history {start final : E.History} (reach : E.HistoryReaches start final) :
    T.HistoryReaches (restriction.history start) (restriction.history final) :=
  let ⟨fuel, within⟩ := reach
  ⟨fuel, restriction.reachesWithin_history within⟩

/-- Every ancestor of an embedded history is itself embedded. -/
theorem exists_of_historyReaches {ancestor : T.History} {final : E.History}
    (reach : T.HistoryReaches ancestor (restriction.history final)) :
    ∃ start, restriction.history start = ancestor ∧ E.HistoryReaches start final := by
  obtain ⟨fuel, within⟩ := reach
  have shorter : ancestor.trace.length ≤ final.trace.length :=
    (restriction.length final) ▸ within.trace_length_le
  obtain ⟨start, steps, length, reaches⟩ := E.exists_ancestor_of_le final shorter
  exact ⟨start, ReachesWithin.eq_start_of_same_length (restriction.reachesWithin_history reaches)
    within ((restriction.length start).trans length), steps, reaches⟩

/-- The embedding of histories reflects reachability. -/
theorem historyReaches_history_iff {start final : E.History} :
    T.HistoryReaches (restriction.history start) (restriction.history final) ↔
      E.HistoryReaches start final := by
  refine ⟨fun reach => ?_, restriction.historyReaches_history⟩
  obtain ⟨other, same, reaches⟩ := restriction.exists_of_historyReaches reach
  rwa [restriction.history.injective same] at reaches

/-- Play passes through an embedded history exactly when its source play passes
through the original. -/
theorem cone_preimage (start : E.History) :
    restriction.history ⁻¹' {final | T.HistoryReaches (restriction.history start) final} =
      {final | E.HistoryReaches start final} :=
  Set.ext fun _ => restriction.historyReaches_history_iff

/-- No embedded play passes through a history of a retained site that takes a
new action. -/
theorem cone_preimage_eq_empty (who : ι) (site : M.InformationSite who)
    (history : N.InformationHistory who (restriction.site who site).1)
    (outside : history ∉ Set.range (restriction.informationHistory who site)) :
    restriction.history ⁻¹' {final | T.HistoryReaches history.1 final} = ∅ := by
  ext final
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro reach
  obtain ⟨start, same, -⟩ := restriction.exists_of_historyReaches reach
  have observed : M.infoOf who start.trace = site.1 := by
    apply (restriction.information who).injective
    rw [← restriction.observed, same]
    exact history.2
  exact outside ⟨⟨start, observed⟩, Subtype.ext same⟩

/-- Play passes through a retained site exactly when its source play passes
through the original site. -/
theorem passage_preimage (who : ι) (site : M.InformationSite who) :
    restriction.history ⁻¹' {final | ∃ history, N.infoOf who history.trace =
        (restriction.site who site).1 ∧ T.HistoryReaches history final} =
      {final | ∃ history, M.infoOf who history.trace = site.1 ∧
        E.HistoryReaches history final} := by
  ext final
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ancestor, observed, reach⟩
    obtain ⟨start, rfl, reaches⟩ := restriction.exists_of_historyReaches reach
    refine ⟨start, (restriction.information who).injective ?_, reaches⟩
    rw [← restriction.observed]
    exact observed
  · rintro ⟨start, observed, reaches⟩
    refine ⟨restriction.history start, ?_, restriction.historyReaches_history reaches⟩
    rw [restriction.observed, observed]
    rfl

variable [Fintype ι]

/-- **Retained beliefs converge without a common depth.** Beliefs at a
retained site follow from a bound on terminal laws. The dominating factors'
loss must be negligible relative to the retained site's mass in the smaller
protocol. Unlike
`GameTheory.Protocol.InformationModel.ActionRestriction.retained_beliefs_converge`,
the histories of the site may lie at different depths. -/
theorem retained_beliefs_converge_unclocked
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (sourceSequence : ℕ → M.BehavioralAssessment)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (sourceMixed : ∀ n, (sourceSequence n).IsFullyMixed)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent M
      (sourceSequence n) sourceAntichain)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N
      (targetSequence n) targetAntichain)
    (who : ι) (site : M.InformationSite who)
    (factor : ℕ → ℝ) (positive : ∀ n, 0 < factor n)
    (atMostOne : ∀ n, factor n ≤ 1)
    (lower : ∀ n final, factor n *
      (((M.runBehavioralTerminalFrom sourceCertificate (sourceSequence n).strategy
        E.initHistory).map restriction.history) final).toReal ≤
          ((N.runBehavioralTerminalFrom targetCertificate (targetSequence n).strategy
            T.initHistory) final).toReal)
    (negligible : Tendsto (fun n => (1 - factor n) /
      (factor n * (M.informationMass (sourceSequence n).strategy who site).toReal)) atTop
        (nhds 0))
    (limit : PMF (M.InformationHistory who site.1))
    (converges : PMFConvergesPointwise (fun n => (sourceSequence n).belief who site) limit) :
    PMFConvergesPointwise
      (fun n => (targetSequence n).belief who (restriction.site who site))
      (limit.map (restriction.informationHistory who site)) := by
  classical
  let sourceLaw (n : ℕ) := (M.runBehavioralTerminalFrom sourceCertificate
    (sourceSequence n).strategy E.initHistory).map restriction.history
  let targetLaw (n : ℕ) :=
    N.runBehavioralTerminalFrom targetCertificate (targetSequence n).strategy T.initHistory
  let passage : Set T.History := {final | ∃ history, N.infoOf who history.trace =
    (restriction.site who site).1 ∧ T.HistoryReaches history final}
  have sourceMass (n : ℕ) :=
    M.informationMass_pos_of_fullSupport _ (sourceMixed n) who site
  have targetMass (n : ℕ) :=
    N.informationMass_pos_of_fullSupport _ (targetMixed n) who (restriction.site who site)
  have sourcePassage (n : ℕ) : (sourceLaw n).toOuterMeasure passage =
      M.informationMass (sourceSequence n).strategy who site := by
    rw [PMF.toOuterMeasure_map_apply, restriction.passage_preimage,
      M.informationMass_eq_passage sourceCertificate _ who site (sourceAntichain who site)]
  have targetPassage (n : ℕ) : (targetLaw n).toOuterMeasure passage =
      N.informationMass (targetSequence n).strategy who (restriction.site who site) :=
    (N.informationMass_eq_passage targetCertificate _ who _ (targetAntichain who _)).symm
  have sourcePositive (n : ℕ) : 0 < ((sourceLaw n).toOuterMeasure passage).toReal := by
    rw [sourcePassage]
    exact ENNReal.toReal_pos (sourceMass n).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one _ who site (sourceAntichain who site)))
  have targetPositive (n : ℕ) : 0 < ((targetLaw n).toOuterMeasure passage).toReal := by
    rw [targetPassage]
    exact ENNReal.toReal_pos (targetMass n).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (N.informationMass_le_one _ who _ (targetAntichain who _)))
  rw [pmfConvergesPointwise_iff_toReal]
  intro history
  let cone : Set T.History := {final | T.HistoryReaches history.1 final}
  have inside : cone ⊆ passage := fun final reach => ⟨history.1, history.2, reach⟩
  have targetRatio (n : ℕ) :
      ((targetLaw n).toOuterMeasure cone).toReal / ((targetLaw n).toOuterMeasure passage).toReal =
        ((targetSequence n).belief who (restriction.site who site) history).toReal := by
    rw [bayes_belief_eq (targetSequence n) who _ (targetAntichain who _) (targetMass n)
      (targetBayes n who _ (targetMass n)), N.bayesBelief_apply_eq_passage targetCertificate,
      ENNReal.toReal_div]
  have sourceLimit : Tendsto (fun n => ((sourceLaw n).toOuterMeasure cone).toReal /
      ((sourceLaw n).toOuterMeasure passage).toReal) atTop
        (nhds ((limit.map (restriction.informationHistory who site)) history).toReal) := by
    by_cases embedded : history ∈ Set.range (restriction.informationHistory who site)
    · obtain ⟨original, rfl⟩ := embedded
      rw [pmf_map_apply_of_injective _ (restriction.informationHistory who site).injective]
      refine (converges.toReal original).congr fun n => ?_
      rw [bayes_belief_eq (sourceSequence n) who site (sourceAntichain who site) (sourceMass n)
        (sourceBayes n who site (sourceMass n)), M.bayesBelief_apply_eq_passage sourceCertificate,
        ENNReal.toReal_div, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
        restriction.passage_preimage]
      simp only [cone, informationHistory_val, restriction.cone_preimage]
    · have zero : (limit.map (restriction.informationHistory who site)) history = 0 := by
        rw [PMF.apply_eq_zero_iff, PMF.support_map]
        rintro ⟨original, -, same⟩
        exact embedded ⟨original, same⟩
      rw [zero, ENNReal.toReal_zero]
      refine tendsto_const_nhds.congr fun n => ?_
      rw [PMF.toOuterMeasure_map_apply, restriction.cone_preimage_eq_empty who site history
        embedded, MeasureTheory.measure_empty, ENNReal.toReal_zero, zero_div]
  exact (conditional_domination_converges_of_subset sourceLaw targetLaw passage cone inside
    sourcePositive targetPositive factor positive atMostOne lower
    (by simpa only [sourcePassage] using negligible) _ sourceLimit).congr targetRatio

section Extension

variable [DecidableEq ι] [Finite T.History] [∀ i, DecidableEq (N.InfoState i)]

open ExecutionProtocol

/-- **Consistent extension without a common depth.** Keep a consistent
assessment of the smaller protocol at retained sites and complete all new
sites. Unlike
`GameTheory.Protocol.InformationModel.ActionRestriction.exists_consistent_extension`,
retained sites need no common decision depth: the dominating factor uses the
global horizon that finite histories certify. -/
theorem exists_consistent_extension_unclocked
    (source : M.BehavioralAssessment) (sourceAntichain : M.DecisionInformationAntichain)
    (sourceConsistent : source.IsSequentiallyConsistent sourceAntichain)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (certificate : T.WellFoundedHistories)
    (payoff : ι → T.History → ℝ) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      ∀ who (site : N.InformationSite who), ¬ restriction.Retained who site.1 →
        ∀ law : PMF (N.Choice who site.1),
          (target.continuationContext certificate site (payoff who)).value
              ((target.strategy who).withLaw site.1 law) ≤
            (target.continuationContext certificate site (payoff who)).value
              (target.strategy who) := by
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
  let free : Finset (N.InformationAgent N.playedInformation) :=
    Finset.univ.filter fun agent => ¬ restriction.Retained agent.1 agent.2.1
  obtain ⟨residual, sequence, target, index, played, mixed, bayes,
      increasing, converges, consistent, freeOptimal⟩ :=
    N.exists_consistent_free_agent_payoff_completion decisionRecall fallback certificate payoff
      (fun _ => payoff) (fun _ => 0) tendsto_const_nhds (fun _ _ _ _ => by simp)
        free pinned referenceLaws (fun n agent _ => pinnedFull n agent) referenceFull epsilon
          positive small vanishes
  have perturbs (n : ℕ) : restriction.PerturbsProfile (sourceSequence n).strategy
      reference.strategy (sequence n).strategy (epsilon n) (positive n).le (small n).le := by
    intro who site
    let agent := N.agentAt (restriction.site who site)
    have notFree : agent ∉ free := by
      simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact restriction.retained_site who site
    exact (congrFun (congrFun (played n) who) (restriction.information who site.1)).trans
      ((N.agentBehavior_at N.playedInformation fallback _ agent).trans
        ((ite_eq_right notFree).trans
          (restriction.perturbProfile_perturbs (sourceSequence n).strategy
            reference.strategy (epsilon n) (positive n).le (small n).le who site)))
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
  refine ⟨target, consistent, extendsTarget, ?_, ?_⟩
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
  · intro who site newSite law
    have member : N.agentAt site ∈ free := by
      simp only [free, Finset.mem_filter, Finset.mem_univ, true_and]
      exact newSite
    exact freeOptimal who site member law

/-- **Extension from whole-policy bounds, without a common depth.** Every
sequential equilibrium of the smaller protocol extends when each new action at
a retained site is bounded, under every pair of extending profiles and every
belief at the site, by the value of some whole continuation policy of the
smaller protocol. Retained sites need no common decision depth. -/
theorem sequentialEquilibrium_extends_of_continuation_unclocked
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (sourcePayoff : ι → E.History → ℝ) (targetPayoff : ι → T.History → ℝ)
    (matching : ∀ who history,
      targetPayoff who (restriction.history history) = sourcePayoff who history)
    (comparison : ∀ (sourceProfile : (i : ι) → M.BehavioralPolicy i)
      (targetProfile : (i : ι) → N.BehavioralPolicy i),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ belief : PMF (M.InformationHistory who site.1),
          ∃ alternative : M.BehavioralPolicy who,
            expect belief (fun history => expect (N.runBehavioralTerminalFrom targetCertificate
              (Profile.update (sig := N.behavioralSignature) targetProfile who
                ((targetProfile who).commit (restriction.site who site).1 action))
              (restriction.history history.1)) (targetPayoff who)) ≤
            expect belief (fun history => expect (M.runBehavioralTerminalFrom sourceCertificate
              (Profile.update (sig := M.behavioralSignature) sourceProfile who alternative)
              history.1) (sourcePayoff who)))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate targetPayoff ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, fun who => sourcePayoff who history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).map
          (fun history => (history, fun who => targetPayoff who history)) := by
  classical
  let _ := Fintype.ofFinite T.History
  have _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  obtain ⟨target, consistent, agrees, beliefs, newOptimal⟩ :=
    restriction.exists_consistent_extension_unclocked source sourceAntichain sourceEquilibrium.2
      reference referenceMixed decisionRecall targetCertificate targetPayoff
  have localOptimal : ∀ who (site : N.InformationSite who) (law : PMF (N.Choice who site.1)),
      (target.continuationContext targetCertificate site (targetPayoff who)).value
          ((target.strategy who).withLaw site.1 law) ≤
        (target.continuationContext targetCertificate site (targetPayoff who)).value
          (target.strategy who) := by
    intro who site law
    by_cases retained : restriction.Retained who site.1
    · obtain ⟨original, observed⟩ := retained
      have same : restriction.site who original = site := Subtype.ext observed
      subst site
      apply restriction.retained_localOptimal_of_continuation sourceCertificate targetCertificate
        source target agrees decisionRecall.actsOnceWhereItMatters who original
        (beliefs who original) (sourcePayoff who) (targetPayoff who) (matching who)
        (sourceEquilibrium.1 who original) _ law
      intro action extra
      obtain ⟨alternative, bound⟩ := comparison source.strategy target.strategy agrees who original
        action extra (source.belief who original)
      refine ⟨alternative, ?_⟩
      unfold Context.value
      change expect ((target.belief who (restriction.site who original)).bind _) _ ≤
        expect ((source.belief who original).bind _) _
      rw [beliefs, PMF.bind_map, expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
        expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
      exact bound
    · exact newOptimal who site retained law
  have historyLaw : (M.runBehavioralTerminalFrom sourceCertificate source.strategy
      E.initHistory).map restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory := by
    rw [← restriction.initial]
    exact restriction.terminal_law sourceCertificate targetCertificate _ _ agrees E.initHistory
  refine ⟨target, (BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal N
    decisionRecall target targetCertificate targetPayoff).mpr ⟨consistent, localOptimal⟩, agrees,
    beliefs, historyLaw, ?_⟩
  calc
    _ = ((M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history).map
        (fun history => (history, fun who => targetPayoff who history)) := by
      rw [PMF.map_comp]
      congr 1
      funext history
      exact congrArg (fun values => (restriction.history history, values))
        (funext fun who => (matching who history).symm)
    _ = _ := congrArg (PMF.map _) historyLaw

/-- **Extension from comparators.** It suffices that each new action at a
retained site is bounded by one legal local lottery of the smaller protocol,
under every pair of extending profiles and at every history of the site. -/
theorem sequentialEquilibrium_extends_of_comparator_unclocked
    [∀ i, DecidableEq (M.InfoState i)]
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (sourcePayoff : ι → E.History → ℝ) (targetPayoff : ι → T.History → ℝ)
    (matching : ∀ who history,
      targetPayoff who (restriction.history history) = sourcePayoff who history)
    (comparator : ∀ who (site : M.InformationSite who),
      N.Choice who (restriction.site who site).1 → PMF (M.Choice who site.1))
    (comparison : ∀ (sourceProfile : (i : ι) → M.BehavioralPolicy i)
      (targetProfile : (i : ι) → N.BehavioralPolicy i),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ history : M.InformationHistory who site.1,
          expect (N.runBehavioralTerminalFrom targetCertificate
            (Profile.update (sig := N.behavioralSignature) targetProfile who
              ((targetProfile who).commit (restriction.site who site).1 action))
            (restriction.history history.1)) (targetPayoff who) ≤
          expect (M.runBehavioralTerminalFrom sourceCertificate
            (Profile.update (sig := M.behavioralSignature) sourceProfile who
              ((sourceProfile who).withLaw site.1 (comparator who site action)))
            history.1) (sourcePayoff who))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate targetPayoff ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, fun who => sourcePayoff who history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).map
          (fun history => (history, fun who => targetPayoff who history)) := by
  let _ := Fintype.ofFinite T.History
  have _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  apply restriction.sequentialEquilibrium_extends_of_continuation_unclocked sourceAntichain
    sourceCertificate targetCertificate reference referenceMixed decisionRecall
    sourcePayoff targetPayoff matching _ source sourceEquilibrium
  intro sourceProfile targetProfile agrees who site action extra belief
  refine ⟨(sourceProfile who).withLaw site.1 (comparator who site action), ?_⟩
  exact expect_mono (fun history _ =>
    comparison sourceProfile targetProfile agrees who site action extra history)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

omit [∀ i, DecidableEq (N.InfoState i)] in
/-- **Extension when new choices are harmless.** Every sequential equilibrium
extends when each player either keeps all its choices or is indifferent over
all outcomes of the larger protocol. Indifference must hold at every history,
not merely along equilibrium play. -/
theorem sequentialEquilibrium_extends_of_indifference_unclocked
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (sourcePayoff : ι → E.History → ℝ) (targetPayoff : ι → T.History → ℝ)
    (matching : ∀ who history,
      targetPayoff who (restriction.history history) = sourcePayoff who history)
    (unchangedOrIndifferent : ∀ who,
      (∀ info, Function.Surjective (restriction.choice who info)) ∨
        ∃ constant, ∀ history, targetPayoff who history = constant)
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate targetPayoff ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, fun who => sourcePayoff who history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).map
          (fun history => (history, fun who => targetPayoff who history)) := by
  classical
  let comparator (who : ι) (site : M.InformationSite who)
      (_ : N.Choice who (restriction.site who site).1) : PMF (M.Choice who site.1) :=
    PMF.pure ⟨some site.2.choose_spec.2.choose, site.2.choose_spec.2.choose_spec⟩
  apply restriction.sequentialEquilibrium_extends_of_comparator_unclocked sourceAntichain
    sourceCertificate targetCertificate reference referenceMixed decisionRecall
    sourcePayoff targetPayoff matching comparator _ source sourceEquilibrium
  intro sourceProfile targetProfile _ who site action extra history
  rcases unchangedOrIndifferent who with unchanged | ⟨constant, indifferent⟩
  · exact (extra (unchanged site.1 action)).elim
  · have sourceConstant (final : E.History) : sourcePayoff who final = constant := by
      rw [← matching]
      exact indifferent _
    rw [show targetPayoff who = fun _ => constant from funext indifferent,
      show sourcePayoff who = fun _ => constant from funext sourceConstant, expect_constant,
      expect_constant]

end Extension

end ActionRestriction

end GameTheory.Protocol.InformationModel
