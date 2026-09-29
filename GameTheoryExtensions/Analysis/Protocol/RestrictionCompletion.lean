/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.RestrictionDomination
import GameTheoryExtensions.Analysis.Protocol.RestrictionBeliefs
import GameTheoryExtensions.Analysis.Protocol.AgentCompletionLimit
import GameTheoryExtensions.Math.Probability.RelativeTremble

/-! # Consistent rational completion beyond a source action restriction

Source behavior and beliefs are preserved at retained decisions. All new
decisions are completed simultaneously by perturbed information-agent Nash
equilibria. The proof chooses forbidden trembles relative to actual source
reach, derives target Bayes beliefs from execution-law domination, and extracts
one common limit. Retained-site incentives remain the separate enforcement
obligation; they are not assumed in this construction.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite T.History]
  [∀ who, DecidableEq (N.InfoState who)]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]
  [∀ who (site : N.InformationSite who), Fintype (N.InformationHistory who site.1)]
  (restriction : M.ActionRestriction N)

/-- Preserve a prescribed consistent source assessment and solve all new
information sites, without assuming any target assessment or belief map. -/
theorem exists_consistent_extension
    (source : M.BehavioralAssessment) (sourceAntichain : M.DecisionInformationAntichain)
    (sourceConsistent : source.IsSequentiallyConsistent sourceAntichain)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (horizon : Nat)
    (payoff : T.History → Player → ℝ)
    (depth : ∀ who, N.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth N site (depth who site))
    (within : ∀ who site, depth who site ≤ horizon) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentiallyConsistent
        decisionRecall.decisionInformationAntichain ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      ∀ who (site : N.InformationSite who), ¬ restriction.Retained who site.1 →
        ∀ law : PMF (N.Choice who site.1),
          (target.continuationContext site (fun history => payoff history who)
            (horizon - depth who site)).value ((target.strategy who).withLaw site.1 law) ≤
          (target.continuationContext site (fun history => payoff history who)
            (horizon - depth who site)).value (target.strategy who) := by
  classical
  let _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  let _ := Fintype.ofFinite T.History
  let _ := Fintype.ofFinite (Σ who, M.InformationSite who)
  obtain ⟨sourceSequence, sourceApproximates, sourceConverges⟩ := sourceConsistent
  let mass (n : ℕ) (entry : Σ who, M.InformationSite who) :=
    M.informationMass (sourceSequence n).strategy entry.1 entry.2
  have massPositive (n : ℕ) (entry : Σ who, M.InformationSite who) : 0 < mass n entry :=
    (sourceApproximates n).1.informationMass_pos entry.1 entry.2
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
  let sites (who : Player) : Finset (N.InfoState who) :=
    Finset.univ.image fun history : {history : T.History // ¬ T.terminal history.state} =>
      N.infoOf who history.1.trace
  have covered : N.CoversInformationSites sites horizon := by
    intro history _ running who
    exact Finset.mem_image.mpr ⟨⟨history, running⟩, Finset.mem_univ _, rfl⟩
  have decisionCovered (who : Player) (site : N.InformationSite who) : site.1 ∈ sites who := by
    obtain ⟨history, running, _⟩ := site.2
    exact Finset.mem_image.mpr ⟨⟨history.1, running⟩, Finset.mem_univ _, history.2⟩
  let fallback (who : Player) : N.Policy who := fun info =>
    ((reference.strategy who info).support_nonempty).choose
  let referenceLaws (agent : N.InformationAgent sites) := reference.strategy agent.1 agent.2.1
  have referenceFull (agent : N.InformationAgent sites) : FullSupport (referenceLaws agent) := by
    obtain ⟨history, _, observed⟩ := Finset.mem_image.mp agent.2.2
    dsimp only [referenceLaws]
    rw [← observed]
    by_cases active : T.active history.1.state agent.1
    · obtain ⟨site, same⟩ := N.exists_informationSite_of_active
        agent.1 history.1 history.2 active
      rw [← same]
      exact referenceMixed agent.1 site
    · let _ := N.subsingleton_choice_of_not_active history.1.trace active
      intro choice
      obtain ⟨witness, supported⟩ :=
        (reference.strategy agent.1 (N.infoOf agent.1 history.1.trace)).support_nonempty
      simpa only [Subsingleton.elim witness choice] using supported
  let pinned (n : ℕ) (agent : N.InformationAgent sites) :=
    restriction.perturbProfile (sourceSequence n).strategy reference.strategy
      (epsilon n) (positive n).le (small n).le agent.1 agent.2.1
  have pinnedFull (n : ℕ) (agent : N.InformationAgent sites) : FullSupport (pinned n agent) :=
    restriction.perturbProfile_fullSupport (sourceSequence n).strategy reference.strategy
      (epsilon n) (positive n) (small n).le agent.1 agent.2.1 (referenceFull agent)
  let free : Finset (N.InformationAgent sites) :=
    Finset.univ.filter fun agent => ¬ restriction.Retained agent.1 agent.2.1
  obtain ⟨residual, sequence, target, index, played, mixed, bayes,
      increasing, converges, consistent, freeOptimal⟩ :=
    exists_consistent_free_agent_completion sites fallback horizon decisionRecall covered
      decisionCovered payoff free pinned referenceLaws (fun n agent _ => pinnedFull n agent)
      referenceFull epsilon positive small vanishes
  have perturbs (n : ℕ) : restriction.PerturbsProfile (sourceSequence n).strategy
      reference.strategy (sequence n).strategy (epsilon n) (positive n).le (small n).le := by
    intro who site
    let agent : N.InformationAgent sites :=
      ⟨who, ⟨(restriction.site who site).1, decisionCovered who (restriction.site who site)⟩⟩
    have notFree : agent ∉ free := by
      simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact restriction.retained_site who site
    let laws : (entry : N.InformationAgent sites) → PMF (N.Choice entry.1 entry.2.1) :=
      pinnedTremble (F := N.informationAgentForm sites fallback horizon)
        free (pinned n) referenceLaws (residual n) (epsilon n) (positive n).le (small n).le
    calc
      _ = N.agentBehavior sites fallback laws agent.1 agent.2.1 :=
        congrFun (congrFun (played n) who) (restriction.information who site.1)
      _ = laws agent := N.agentBehavior_at sites fallback laws agent
      _ = pinned n agent := by exact ite_eq_right notFree
      _ = _ := restriction.perturbProfile_perturbs (sourceSequence n).strategy reference.strategy
        (epsilon n) (positive n).le (small n).le who site
  have sourceAlong : BehavioralAssessmentConvergesPointwise
      (fun n => sourceSequence (index n)) source :=
    ⟨fun who site => (sourceConverges.strategy who site).subsequence increasing,
      fun who site => (sourceConverges.belief who site).subsequence increasing⟩
  have extendsTarget : restriction.ExtendsProfile source.strategy target.strategy :=
    restriction.extendsProfile_of_perturbs_converges reference.strategy
      (fun n => sourceSequence (index n)) source (fun n => sequence (index n)) target
      (sourceApproximates (index 0)).1 sourceAlong converges
      (fun n => epsilon (index n)) (fun n => (positive (index n)).le)
      (fun n => (small (index n)).le) (vanishes.comp increasing.tendsto_atTop)
      (fun n => perturbs (index n))
  refine ⟨target, consistent, extendsTarget, ?_, ?_⟩
  · intro who site
    let elapsed := depth who (restriction.site who site)
    let steps := Fintype.card Player * elapsed
    let factor (n : ℕ) := (1 - epsilon n) ^ steps
    have factorPositive (n : ℕ) : 0 < factor n := pow_pos (sub_pos.mpr (small n)) _
    have factorBound (n : ℕ) : factor n ≤ 1 :=
      pow_le_one₀ (sub_pos.mpr (small n)).le (by linarith [positive n])
    have negligible : Tendsto (fun n => (1 - factor n) /
        (factor n * M.informationMass (sourceSequence n).strategy who site)) atTop (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact div_nonneg (sub_nonneg.mpr (factorBound n))
          (mul_nonneg (factorPositive n).le
            ((sourceApproximates n).1.informationMass_pos who site).le)
      · intro n
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr (factorBound n))
          (mul_pos (factorPositive n) (reachPositive n))
          (mul_le_mul_of_nonneg_left (reachBound n ⟨who, site⟩) (factorPositive n).le)
      · exact relativeTremble_power_ratio_tendsto reach reachPositive steps
    have beliefs := restriction.retained_beliefs_converge sourceSequence sequence
      sourceAntichain decisionRecall.decisionInformationAntichain
      (fun n => (sourceApproximates n).1) mixed (fun n => (sourceApproximates n).2) bayes
      who site elapsed (clock who (restriction.site who site)) factor factorPositive factorBound
      (fun n history => restriction.perturbed_run_domination (sourceSequence n).strategy
        reference.strategy (sequence n).strategy (epsilon n) (positive n).le (small n).le
        (perturbs n) elapsed history)
      negligible (source.belief who site) (sourceConverges.belief who site)
    exact (converges.belief who (restriction.site who site)).unique
      (beliefs.subsequence increasing)
  · intro who site newSite law
    have member :
        (⟨who, ⟨site.1, decisionCovered who site⟩⟩ : N.InformationAgent sites) ∈ free := by
      simp only [free, Finset.mem_filter, Finset.mem_univ, true_and]
      exact newSite
    exact freeOptimal who site (decisionCovered who site) member
      (depth who site) (horizon - depth who site) (clock who site)
      (by have := within who site; omega) law

end GameTheory.Protocol.InformationModel.ActionRestriction
