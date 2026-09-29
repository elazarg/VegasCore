/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity

/-! # Uniform whole-policy regret at finite assessment limits

Finite decision menus form a compact product of probability simplices. Thus
joint continuation-value continuity controls every alternative policy uniformly,
even when the alternative changes with the perturbation. This argument needs
neither recall nor Bayes consistency: it compares whole continuation policies
directly with an assessment already known to be sequentially rational.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E} [Finite E.History]

omit [Fintype Player] [DecidableEq Player] in
private theorem policy_subsequence (who : Player) (policies : ℕ → M.BehavioralPolicy who) :
    ∃ policy : M.BehavioralPolicy who, ∃ index : ℕ → ℕ, StrictMono index ∧
      ∀ site : M.InformationSite who,
        PMFConvergesPointwise (fun n => policies (index n) site.1) (policy site.1) := by
  classical
  obtain ⟨laws, index, increasing, converges⟩ :=
    exists_subseq_pmfConvergesPointwise_pi
      (fun n (site : M.InformationSite who) => policies n site.1)
  let policy : M.BehavioralPolicy who := fun info =>
    if decision : M.IsDecisionInfo who info then laws ⟨info, decision⟩ else policies 0 info
  refine ⟨policy, index, increasing, ?_⟩
  intro site
  simp only [policy, site.2, ↓reduceDIte]
  exact converges site

private theorem uniform_gain_at_site
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : Player) (site : M.InformationSite who) (payoff : E.History → ℝ) (fuel : Nat)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff fuel)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (alternative : M.BehavioralPolicy who),
        ((sequence n).continuationContext site payoff fuel).value alternative -
          ((sequence n).continuationContext site payoff fuel).value
            ((sequence n).strategy who) ≤ error n := by
  classical
  let gain (n : ℕ) (alternative : M.BehavioralPolicy who) : ℝ :=
    ((sequence n).continuationContext site payoff fuel).value alternative -
      ((sequence n).continuationContext site payoff fuel).value ((sequence n).strategy who)
  obtain ⟨upper, above⟩ := (Set.finite_range payoff).bddAbove
  obtain ⟨lower, below⟩ := (Set.finite_range payoff).bddBelow
  have bounded (n : ℕ) : BddAbove (Set.range (gain n)) := by
    refine ⟨upper - lower, ?_⟩
    rintro value ⟨alternative, rfl⟩
    apply sub_le_sub
    · change expect (((sequence n).continuationContext site payoff fuel).outcome alternative)
        payoff ≤ upper
      exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) upper
        fun history _ => above (Set.mem_range_self history)
    · change lower ≤ expect (((sequence n).continuationContext site payoff fuel).outcome
        ((sequence n).strategy who)) payoff
      rw [← expect_constant (((sequence n).continuationContext site payoff fuel).outcome
        ((sequence n).strategy who)) lower]
      exact expect_mono (fun history _ => below (Set.mem_range_self history))
        (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  let error (n : ℕ) := max 0 (sSup (Set.range (gain n)))
  have nonnegative (n : ℕ) : 0 ≤ error n := le_max_left _ _
  have bound (n : ℕ) (alternative : M.BehavioralPolicy who) : gain n alternative ≤ error n :=
    (le_csSup (bounded n) (Set.mem_range_self alternative)).trans (le_max_right _ _)
  refine ⟨error, nonnegative, ?_, bound⟩
  apply tendsto_order.mpr
  constructor
  · intro value negative
    exact Eventually.of_forall fun n => negative.trans_le (nonnegative n)
  · intro epsilon positive
    by_contra fails
    obtain ⟨first, firstIncreasing, bad⟩ :=
      extraction_of_frequently_atTop (not_eventually.mp fails)
    have deviations (n : ℕ) : ∃ alternative : M.BehavioralPolicy who,
        epsilon / 2 < gain (first n) alternative := by
      have large : epsilon ≤ sSup (Set.range (gain (first n))) := by
        have notSmall := not_lt.mp (bad n)
        change epsilon ≤ max 0 (sSup (Set.range (gain (first n)))) at notSmall
        exact (le_max_iff.mp notSmall).resolve_left (not_le.mpr positive)
      obtain ⟨value, ⟨alternative, rfl⟩, greater⟩ := exists_lt_of_lt_csSup
        (show (Set.range (gain (first n))).Nonempty from
          ⟨_, Set.mem_range_self ((sequence (first n)).strategy who)⟩) (show epsilon / 2 <
          sSup (Set.range (gain (first n))) by linarith)
      exact ⟨alternative, greater⟩
    choose alternatives greater using deviations
    obtain ⟨alternative, second, secondIncreasing, policyConverges⟩ :=
      policy_subsequence who alternatives
    have selectedConverges : BehavioralAssessmentConvergesPointwise
        (fun n => sequence (first (second n))) assessment :=
      ⟨fun player decision => (converges.strategy player decision).subseq
          (firstIncreasing.comp secondIncreasing),
        fun player decision => (converges.belief player decision).subseq
          (firstIncreasing.comp secondIncreasing)⟩
    have alternate := selectedConverges.context_value (.of_finite_history E) site payoff fuel
      (fun n => alternatives (second n)) alternative policyConverges
    have prescribed := selectedConverges.context_value (.of_finite_history E) site payoff fuel
      (fun n => (sequence (first (second n))).strategy who) (assessment.strategy who)
      (selectedConverges.strategy who)
    have limitBound := le_of_tendsto_of_tendsto tendsto_const_nhds (alternate.sub prescribed)
      (Eventually.of_forall fun n => (greater (second n)).le)
    have optimal := (Context.isLocallyOptimal_iff_of_integrable
      (continuationContext_integrableAt_of_finite (.of_finite_history E) assessment site payoff
        fuel _)
      fun alternative _ => continuationContext_integrableAt_of_finite (.of_finite_history E)
        assessment site payoff fuel alternative).mp rational alternative (Set.mem_univ _)
    linarith

/-- Sequential rationality of a finite assessment controls every whole
continuation policy uniformly along any convergent assessment sequence. The
sequence itself need not be fully mixed, Bayesian, or sequentially rational. -/
theorem BehavioralAssessmentConvergesPointwise.exists_uniform_policy_gain_bound
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : Player) (payoff : E.History → ℝ) (fuel : Nat)
    (rational : ∀ site : M.InformationSite who, assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff fuel)) :
    ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n (site : M.InformationSite who) (alternative : M.BehavioralPolicy who),
        ((sequence n).continuationContext site payoff fuel).value alternative -
          ((sequence n).continuationContext site payoff fuel).value
            ((sequence n).strategy who) ≤ error n := by
  classical
  let _ := Fintype.ofFinite (M.InformationSite who)
  choose errors nonnegative vanishes bounds using fun site =>
    uniform_gain_at_site converges who site payoff fuel (rational site)
  let error (n : ℕ) := ∑ site, errors site n
  refine ⟨error, (fun n => Finset.sum_nonneg fun site _ => nonnegative site n), ?_, ?_⟩
  · simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun site _ => vanishes site)
  · intro n site alternative
    exact (bounds site n alternative).trans
      (Finset.single_le_sum (fun other _ => nonnegative other n) (Finset.mem_univ site))

end GameTheory.Protocol.InformationModel
