/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion
import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Continuity of finite behavioral continuation values

Only reachable decision menus and transition laws need be finite. No finite
carrier of private memory or all raw actions is assumed. Finite-horizon
execution and continuation expectations respect pointwise convergence of
decision laws and beliefs.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

/-- The expectation of a fixed finitely supported law converges along
observables converging on its support. -/
theorem expect_tendsto_of_support_finite {α : Type*} (law : PMF α)
    (finite : law.support.Finite) (values : ℕ → α → ℝ) (value : α → ℝ)
    (converges : ∀ entry ∈ law.support,
      Tendsto (fun n => values n entry) atTop (nhds (value entry))) :
    Tendsto (fun n => expect law (values n)) atTop (nhds (expect law value)) := by
  simp_rw [expect_eq_sum_of_support_finite law finite]
  exact tendsto_finsetSum _ fun entry supported =>
    (converges entry (finite.mem_toFinset.mp supported)).const_mul ((law entry).toReal)

/-- A finitely supported outer law passes convergence of its integrable
supported branches to the dependent bind. -/
theorem expect_bindOnSupport_tendsto_of_support_finite {α β : Type*} (law : PMF α)
    (finite : law.support.Finite)
    (kernels : ℕ → ∀ entry ∈ law.support, PMF β)
    (kernel : ∀ entry ∈ law.support, PMF β) (payoff : β → ℝ)
    (integrable : ∀ n entry supported, PayoffIntegrable (kernels n entry supported) payoff)
    (limitIntegrable : ∀ entry supported, PayoffIntegrable (kernel entry supported) payoff)
    (converges : ∀ entry (supported : entry ∈ law.support),
      Tendsto (fun n => expect (kernels n entry supported) payoff) atTop
        (nhds (expect (kernel entry supported) payoff))) :
    Tendsto (fun n => expect (law.bindOnSupport (kernels n)) payoff) atTop
      (nhds (expect (law.bindOnSupport kernel) payoff)) := by
  classical
  let value (next : ∀ entry ∈ law.support, PMF β) (entry : α) : ℝ :=
    if supported : entry ∈ law.support then expect (next entry supported) payoff else 0
  have tower (next : ∀ entry ∈ law.support, PMF β)
      (branches : ∀ entry supported, PayoffIntegrable (next entry supported) payoff) :
      expect (law.bindOnSupport next) payoff = expect law (value next) :=
    expect_bindOnSupport_tower_on_support law next payoff
      (payoffIntegrable_bindOnSupport_of_finite_support law next payoff finite branches)
      (value next) fun entry supported => by simp only [value, supported, ↓reduceDIte]
  have sequenceTower (n : ℕ) := tower (kernels n) (integrable n)
  simp_rw [sequenceTower, tower kernel limitIntegrable]
  apply expect_tendsto_of_support_finite law finite
  intro entry supported
  simpa only [value, supported, ↓reduceDIte] using converges entry supported

/-- Removing a vanishing full-support perturbation retains the same law
limit, even when the unperturbed response varies along the sequence. -/
theorem PMFConvergesPointwise.of_mix_vanishing {α : Type*}
    (reference : PMF α) (responses : ℕ → PMF α) (limit : PMF α)
    (weight : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ weight n)
    (belowOne : ∀ n, weight n < 1) (vanishes : Tendsto weight atTop (nhds 0))
    (converges : PMFConvergesPointwise
      (fun n => mix (weight n) (nonnegative n) (belowOne n).le reference (responses n))
      limit) : PMFConvergesPointwise responses limit := by
  rw [pmfConvergesPointwise_iff_toReal] at converges ⊢
  intro value
  have numerator := (converges value).sub (vanishes.mul_const ((reference value).toReal))
  have denominator := (tendsto_const_nhds (x := (1 : ℝ))).sub vanishes
  have quotient := numerator.div denominator (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have same (n : ℕ) :
      (((mix (weight n) (nonnegative n) (belowOne n).le reference (responses n)) value).toReal -
          weight n * (reference value).toReal) / (1 - weight n) =
        ((responses n) value).toReal := by
    rw [mix_apply_toReal]
    have nonzero : 1 - weight n ≠ 0 := (sub_pos.mpr (belowOne n)).ne'
    field_simp
    ring
  simp only [zero_mul, sub_zero, div_one] at quotient
  exact quotient.congr' (Filter.Eventually.of_forall same)

end GameTheory.Math.Probability

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type} [Fintype ι] {E : ExecutionProtocol ι} {M : InformationModel E}

omit [Fintype ι] in
/-- Finite decision menus make every current menu finite: a player that is not
active has only the empty choice. -/
theorem finite_current_choice [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (history : E.History) (running : ¬ E.terminal history.state) (who : ι) :
    Finite (M.Choice who (M.infoOf who history.trace)) := by
  by_cases active : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history running active
    rw [← same]
    infer_instance
  · let _ := M.subsingleton_choice_of_not_active history.trace active
    infer_instance

/-- Finite decision menus and finitely supported transitions give every
finite-horizon behavioral run a finite support. -/
theorem runBehavioralFrom_support_finite
    [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (transitions : E.FiniteTransitions)
    (profile : ∀ who, M.BehavioralPolicy who) (fuel : ℕ) (history : E.History) :
    (M.runBehavioralFrom profile fuel history).support.Finite := by
  induction fuel generalizing history with
  | zero =>
      simpa only [InformationModel.runBehavioralFrom, ExecutionProtocol.runRandomizedFor_zero,
        PMF.support_pure] using Set.finite_singleton history
  | succ fuel induction =>
      by_cases terminal : E.terminal history.state
      · rw [M.runBehavioralFrom_of_terminal _ _ terminal]
        simpa only [PMF.support_pure] using Set.finite_singleton history
      · let _ (who : ι) : Finite (M.Choice who (M.infoOf who history.trace)) :=
          finite_current_choice history terminal who
        rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel terminal, PMF.support_bind]
        have joint : (M.behavioralJoint profile history.trace terminal).support.Finite := by
          unfold InformationModel.behavioralJoint
          rw [PMF.support_map]
          exact (Set.toFinite _).image _
        apply joint.biUnion
        intro draw _
        rw [PMF.support_bindOnSupport]
        exact (transitions history terminal draw).biUnion' fun target realized =>
          induction (history.extend draw.2 realized)

theorem runBehavioralFrom_expect_tendsto
    [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (transitions : E.FiniteTransitions)
    (sequence : ℕ → ∀ who, M.BehavioralPolicy who)
    (profile : ∀ who, M.BehavioralPolicy who)
    (converges : ∀ who (site : M.InformationSite who),
      PMFConvergesPointwise (fun n => sequence n who site.1) (profile who site.1))
    (payoff : E.History → ℝ) (fuel : ℕ) (history : E.History) :
    Tendsto (fun n => expect (M.runBehavioralFrom (sequence n) fuel history) payoff) atTop
      (nhds (expect (M.runBehavioralFrom profile fuel history) payoff)) := by
  classical
  induction fuel generalizing history with
  | zero => exact tendsto_const_nhds
  | succ fuel induction =>
      by_cases terminal : E.terminal history.state
      · simp only [M.runBehavioralFrom_of_terminal _ _ terminal]
        exact tendsto_const_nhds
      · let _ (who : ι) : Finite (M.Choice who (M.infoOf who history.trace)) :=
          finite_current_choice history terminal who
        let _ : Fintype (∀ who, M.Choice who (M.infoOf who history.trace)) :=
          Fintype.ofFinite _
        have current (who : ι) : PMFConvergesPointwise
            (fun n => sequence n who (M.infoOf who history.trace))
            (profile who (M.infoOf who history.trace)) := by
          by_cases active : E.active history.state who
          · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history terminal active
            rw [← same]
            exact converges who site
          · have equal (n : ℕ) := M.behavioral_eq_of_not_active (sequence n who)
              (profile who) history.trace active
            simp_rw [equal]
            exact pmfConvergesPointwise_const _
        let continuation (policies : ∀ who, M.BehavioralPolicy who)
            (draw : { joint : ∀ i, Option (E.Action i) // E.Legal history.state joint }) :
            PMF E.History :=
          (E.step history.state draw).bindOnSupport fun _ realized =>
            M.runBehavioralFrom policies fuel (history.extend draw.2 realized)
        have continuationIntegrable (policies : ∀ who, M.BehavioralPolicy who) draw :
            PayoffIntegrable (continuation policies draw) payoff :=
          payoffIntegrable_bindOnSupport_of_finite_support _ _ _ (transitions history terminal draw)
            fun _ _ => payoffIntegrable_of_finite_support _ _
              (runBehavioralFrom_support_finite transitions policies fuel _)
        have factor (policies : ∀ who, M.BehavioralPolicy who) :
            expect (M.runBehavioralFrom policies (fuel + 1) history) payoff =
              expect (independentProduct fun who => policies who (M.infoOf who history.trace))
                fun choices => expect (continuation policies ⟨fun who => (choices who).1,
                  legal_of_legalOption terminal fun who =>
                    (M.menu_adequate who history.trace (choices who).1).mp
                      (choices who).2⟩) payoff := by
          have integrable := payoffIntegrable_of_finite_support _ payoff
            (runBehavioralFrom_support_finite transitions policies (fuel + 1) history)
          rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel terminal] at integrable ⊢
          rw [expect_bind_tower _ _ _ integrable, behavioralJoint, expect_map]
          rfl
        simp_rw [factor]
        apply (PMFConvergesPointwise.independentProduct current).expect_varying_finite
        intro choices
        apply expect_bindOnSupport_tendsto_of_support_finite _ (transitions history terminal _)
        · exact fun n _ _ => payoffIntegrable_of_finite_support _ _
            (runBehavioralFrom_support_finite transitions (sequence n) fuel _)
        · exact fun _ _ => payoffIntegrable_of_finite_support _ _
            (runBehavioralFrom_support_finite transitions profile fuel _)
        intro target realized
        exact induction _

/-- Reach weights converge with the behavioral strategies. A reach weight is a
finite product along one trace, so no finiteness of menus or transitions is
needed. -/
theorem BehavioralAssessmentConvergesPointwise.historyReachWeight
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (history : E.History) :
    Tendsto (fun n => M.historyReachWeight (sequence n).strategy history) atTop
      (nhds (M.historyReachWeight assessment.strategy history)) := by
  classical
  apply (ENNReal.tendsto_toReal_iff (fun _ => PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  obtain ⟨state, trace⟩ := history
  induction trace with
  | start => exact tendsto_const_nhds
  | @extend source target prior joint legal realized induction =>
      change Tendsto (fun n => (M.historyReachWeight (sequence n).strategy
          ⟨target, prior.extend joint legal realized⟩).toReal) atTop
        (nhds (M.historyReachWeight assessment.strategy
          ⟨target, prior.extend joint legal realized⟩).toReal)
      change Tendsto (fun n => (M.historyReachWeight (sequence n).strategy
          ⟨source, prior⟩).toReal) atTop
        (nhds (M.historyReachWeight assessment.strategy ⟨source, prior⟩).toReal) at induction
      refine Tendsto.congr (fun n => (historyReachProbability_extend M (sequence n).strategy
        prior joint legal realized).symm) ?_
      rw [historyReachProbability_extend M assessment.strategy prior joint legal realized]
      simp only [stepProb]
      apply induction.mul
      apply Tendsto.mul_const
      simp only [behavioralJoint_prob_eq_prod]
      apply tendsto_finsetProd
      intro player _
      by_cases active : E.active source player
      · obtain ⟨⟨info, decision⟩, same⟩ :=
          M.exists_informationSite_of_active player ⟨source, prior⟩ legal.1 active
        change info = M.infoOf player prior at same
        subst same
        exact (converges.strategy player ⟨_, decision⟩).toReal _
      · simp only [M.behavioral_eq_of_not_active ((sequence _).strategy player)
          (assessment.strategy player) prior active]
        exact tendsto_const_nhds

theorem BehavioralAssessmentConvergesPointwise.informationMass
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : ι) (site : M.InformationSite who)
    [Finite (M.InformationHistory who site.1)] :
    Tendsto (fun n => M.informationMass (sequence n).strategy who site) atTop
      (nhds (M.informationMass assessment.strategy who site)) := by
  let _ : Fintype (M.InformationHistory who site.1) := Fintype.ofFinite _
  simp only [InformationModel.informationMass, tsum_fintype]
  exact tendsto_finsetSum Finset.univ fun history _ => converges.historyReachWeight history.1

/-- Sequential consistency enforces ordinary Bayes conditioning at every
positive-mass information set of the limit strategy. Off-path beliefs remain
those supplied by the common approximating sequence. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.isBayesConsistent
    {assessment : M.BehavioralAssessment}
    [∀ who (site : M.InformationSite who), Finite (M.InformationHistory who site.1)]
    (antichain : M.DecisionInformationAntichain)
    (consistent : assessment.IsSequentiallyConsistent antichain) :
    BehavioralAssessment.IsBayesConsistent M assessment antichain := by
  obtain ⟨sequence, approximates, converges⟩ := consistent
  intro who site positive history
  have ratios := ENNReal.Tendsto.div
    (converges.historyReachWeight history.1) (Or.inr positive.ne')
    (converges.informationMass who site)
    (Or.inl (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one assessment.strategy who site (antichain who site))))
  have equality (n : ℕ) : (sequence n).belief who site history =
      M.historyReachWeight (sequence n).strategy history.1 /
        M.informationMass (sequence n).strategy who site :=
    (approximates n).2 who site
      (M.informationMass_pos_of_fullSupport _ (approximates n).1 who site) history
  exact tendsto_nhds_unique (converges.belief who site history)
    (ratios.congr' (Filter.Eventually.of_forall fun n => (equality n).symm))

variable [DecidableEq ι]

omit [Fintype ι] in
theorem continuationContext_integrableAt_of_finite
    [Fintype ι] [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (transitions : E.FiniteTransitions)
    (assessment : M.BehavioralAssessment) {who : ι} (site : M.InformationSite who)
    [Finite (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ) (alternative : M.BehavioralPolicy who) :
    (assessment.continuationContext site payoff fuel).IntegrableAt alternative :=
  payoffIntegrable_bind_of_finite _ _ _ fun _ => payoffIntegrable_of_finite_support _ _
    (runBehavioralFrom_support_finite transitions _ fuel _)

theorem BehavioralAssessmentConvergesPointwise.context_value
    [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (transitions : E.FiniteTransitions)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    {who : ι} (site : M.InformationSite who)
    [Finite (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (alternatives : ℕ → M.BehavioralPolicy who) (alternative : M.BehavioralPolicy who)
    (alternativesConverge : ∀ decision : M.InformationSite who,
      PMFConvergesPointwise (fun n => alternatives n decision.1) (alternative decision.1)) :
    Tendsto (fun n => ((sequence n).continuationContext site payoff fuel).value
      (alternatives n)) atTop
      (nhds ((assessment.continuationContext site payoff fuel).value alternative)) := by
  let _ : Fintype (M.InformationHistory who site.1) := Fintype.ofFinite _
  have tower (current : M.BehavioralAssessment) (policy : M.BehavioralPolicy who) :=
    current.continuationContext_value_tower site payoff fuel policy
      (continuationContext_integrableAt_of_finite transitions current site payoff fuel policy)
  simp_rw [tower]
  apply (converges.belief who site).expect_varying_finite
  intro history
  apply runBehavioralFrom_expect_tendsto transitions
  intro player decision
  by_cases same : player = who
  · subst player
    simpa only [Profile.update_same] using alternativesConverge decision
  · simpa only [Profile.update_of_ne _ _ same] using converges.strategy player decision

/-- Optimal response policies may be chosen separately from the fully mixed
assessment strategies. If both converge to the same prescribed behavior,
their continuation comparisons pass to the limit. This permits the unavoidable
trembles in the approximants without asserting that those trembles are optimal. -/
theorem BehavioralAssessmentConvergesPointwise.rationalAt_of_optimal_responses
    [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (transitions : E.FiniteTransitions)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    {who : ι} (site : M.InformationSite who)
    [Finite (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (responses : ℕ → M.BehavioralPolicy who)
    (responsesConverge : ∀ decision : M.InformationSite who,
      PMFConvergesPointwise (fun n => responses n decision.1)
        (assessment.strategy who decision.1))
    (optimal : ∀ n alternative,
      ((sequence n).continuationContext site payoff fuel).value alternative ≤
        ((sequence n).continuationContext site payoff fuel).value (responses n)) :
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext site payoff fuel) := by
  refine ⟨continuationContext_integrableAt_of_finite transitions assessment site payoff fuel _,
    fun alternative _ =>
      continuationContext_integrableAt_of_finite transitions assessment site payoff fuel _,
    fun alternative _ => ?_⟩
  exact le_of_tendsto_of_tendsto
    (converges.context_value transitions site payoff fuel (fun _ => alternative) alternative
      (fun _ => pmfConvergesPointwise_const _))
    (converges.context_value transitions site payoff fuel responses (assessment.strategy who)
      responsesConverge)
    (Filter.Eventually.of_forall (fun n => optimal n alternative))

end GameTheory.Protocol.InformationModel
