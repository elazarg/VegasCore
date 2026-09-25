/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # Continuity of finite behavioral continuation values

Only reachable decision menus need be finite. A fully mixed finite-support
reference supplies this fact; no finite carrier of private memory or all raw
actions is assumed. Finite-horizon execution and continuation expectations
respect pointwise convergence of decision laws and beliefs.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

theorem FinDistConvergesPointwise.expect_varying {α : Type*} [Finite α]
    {sequence : ℕ → FinDist α} {target : FinDist α}
    (converges : FinDistConvergesPointwise sequence target)
    (values : ℕ → α → ℝ) (value : α → ℝ)
    (valuesConverge : ∀ entry, Tendsto (fun n => values n entry) atTop (nhds (value entry))) :
    Tendsto (fun n => (sequence n).expect (values n)) atTop (nhds (target.expect value)) := by
  let _ := Fintype.ofFinite α
  simp_rw [FinDist.expect_eq_sum]
  exact tendsto_finsetSum Finset.univ fun entry _ =>
    (converges entry).mul (valuesConverge entry)

theorem FinDist.expect_tendsto {α : Type*} (law : FinDist α)
    (values : ℕ → α → ℝ) (value : α → ℝ)
    (converges : ∀ entry ∈ law.support,
      Tendsto (fun n => values n entry) atTop (nhds (value entry))) :
    Tendsto (fun n => law.expect (values n)) atTop (nhds (law.expect value)) := by
  simp_rw [FinDist.expect_eq_sum_support]
  exact tendsto_finsetSum law.supportFinset fun entry supported =>
    (converges entry (FinDist.mem_supportFinset.mp supported)).const_mul (law.prob entry)

theorem FinDist.expect_bindOnSupport_tendsto {α β : Type*} (law : FinDist α)
    (kernels : ℕ → ∀ entry ∈ law.support, FinDist β)
    (kernel : ∀ entry ∈ law.support, FinDist β) (payoff : β → ℝ)
    (converges : ∀ entry (supported : entry ∈ law.support),
      Tendsto (fun n => (kernels n entry supported).expect payoff) atTop
        (nhds ((kernel entry supported).expect payoff))) :
    Tendsto (fun n => (law.bindOnSupport (kernels n)).expect payoff) atTop
      (nhds ((law.bindOnSupport kernel).expect payoff)) := by
  classical
  obtain ⟨fallback, supported⟩ := law.support_nonempty
  let extend (next : ∀ entry ∈ law.support, FinDist β) (entry : α) : FinDist β :=
    if member : entry ∈ law.support then next entry member else kernel fallback supported
  have same (next : ∀ entry ∈ law.support, FinDist β) :
      law.bindOnSupport next = law.bind (extend next) := by
    apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
    intro entry member
    simp only [extend, dite_eq_left member]
  simp_rw [same, FinDist.expect_bind]
  apply law.expect_tendsto
  intro entry member
  simpa only [extend, dite_eq_left member] using converges entry member

/-- Removing a vanishing full-support perturbation retains the same law
limit, even when the unperturbed response varies along the sequence. -/
theorem FinDistConvergesPointwise.of_mix_vanishing {α : Type*}
    (reference : FinDist α) (responses : ℕ → FinDist α) (limit : FinDist α)
    (weight : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ weight n)
    (belowOne : ∀ n, weight n < 1) (vanishes : Tendsto weight atTop (nhds 0))
    (converges : FinDistConvergesPointwise
      (fun n => FinDist.mix (weight n) (nonnegative n) (belowOne n).le reference (responses n))
      limit) : FinDistConvergesPointwise responses limit := by
  intro value
  have numerator := (converges value).sub (vanishes.mul_const (reference.prob value))
  have denominator := (tendsto_const_nhds (x := (1 : ℝ))).sub vanishes
  have quotient := numerator.div denominator (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have same (n : ℕ) :
      ((FinDist.mix (weight n) (nonnegative n) (belowOne n).le reference (responses n)).prob
        value - weight n * reference.prob value) / (1 - weight n) =
          (responses n).prob value := by
    rw [FinDist.prob_mix]
    have nonzero : 1 - weight n ≠ 0 := (sub_pos.mpr (belowOne n)).ne'
    field_simp
    ring
  simp only [zero_mul, sub_zero, div_one] at quotient
  exact quotient.congr' (Filter.Eventually.of_forall same)

end GameTheory.Math.Probability

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type} [Fintype ι] {E : ExecutionProtocol ι} {M : InformationModel E}

theorem runBehavioralFrom_expect_tendsto
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    (sequence : ℕ → ∀ who, M.BehavioralPolicy who)
    (profile : ∀ who, M.BehavioralPolicy who)
    (converges : ∀ who (site : M.InformationSite who),
      FinDistConvergesPointwise (fun n => sequence n who site.1) (profile who site.1))
    (payoff : E.History → ℝ) (fuel : ℕ) (history : E.History) :
    Tendsto (fun n => (M.runBehavioralFrom (sequence n) fuel history).expect payoff) atTop
      (nhds ((M.runBehavioralFrom profile fuel history).expect payoff)) := by
  classical
  induction fuel generalizing history with
  | zero => exact tendsto_const_nhds
  | succ fuel induction =>
      by_cases terminal : E.terminal history.state
      · simp only [M.runBehavioralFrom_of_terminal _ _ terminal]
        exact tendsto_const_nhds
      · have finiteChoices (who : ι) : Finite (M.Choice who (M.infoOf who history.trace)) := by
          by_cases active : E.active history.state who
          · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history terminal active
            rw [← same]
            exact (mixed who site).finite
          · let _ := M.subsingleton_choice_of_not_active history.trace active
            infer_instance
        let _ (who : ι) : Finite (M.Choice who (M.infoOf who history.trace)) := finiteChoices who
        have current (who : ι) : FinDistConvergesPointwise
            (fun n => sequence n who (M.infoOf who history.trace))
            (profile who (M.infoOf who history.trace)) := by
          by_cases active : E.active history.state who
          · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history terminal active
            rw [← same]
            exact converges who site
          · have equal (n : ℕ) := M.behavioral_eq_of_not_active (sequence n who)
              (profile who) history.trace active
            simp_rw [equal]
            exact finDistConvergesPointwise_const _
        simp_rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel terminal,
          behavioralJoint, FinDist.bind_map, FinDist.expect_bind]
        apply (FinDistConvergesPointwise.pi current).expect_varying
        intro choices
        apply FinDist.expect_bindOnSupport_tendsto
        intro target realized
        exact induction _

theorem BehavioralAssessmentConvergesPointwise.historyReachProbability
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (history : E.History) :
    Tendsto (fun n => M.historyReachProbability (sequence n).strategy history) atTop
      (nhds (M.historyReachProbability assessment.strategy history)) := by
  simpa only [GameTheory.Math.Probability.FinDist.expect_prob_pure,
    InformationModel.historyReachProbability, InformationModel.runBehavioral] using
    runBehavioralFrom_expect_tendsto reference mixed (fun n => (sequence n).strategy)
      assessment.strategy converges.strategy
      (fun outcome => (FinDist.pure outcome).prob history) history.trace.length E.initHistory

theorem BehavioralAssessmentConvergesPointwise.informationMass
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] :
    Tendsto (fun n => M.informationMass (sequence n).strategy who site) atTop
      (nhds (M.informationMass assessment.strategy who site)) := by
  unfold InformationModel.informationMass
  exact tendsto_finsetSum Finset.univ fun history _ =>
    converges.historyReachProbability reference mixed history.1

/-- Sequential consistency enforces ordinary Bayes conditioning at every
positive-mass information set of the limit strategy. Off-path beliefs remain
those supplied by the common approximating sequence. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.isBayesConsistent
    {assessment : M.BehavioralAssessment}
    [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]
    (antichain : M.DecisionInformationAntichain)
    (consistent : assessment.IsSequentiallyConsistent antichain) :
    BehavioralAssessment.IsBayesConsistent M assessment antichain := by
  obtain ⟨sequence, approximates, converges⟩ := consistent
  intro who site positive history
  have ratios :=
    (converges.historyReachProbability (sequence 0) (approximates 0).1 history.1).div
      (converges.informationMass (sequence 0) (approximates 0).1 who site) positive.ne'
  have equality (n : ℕ) : ((sequence n).belief who site).prob history =
      M.historyReachProbability (sequence n).strategy history.1 /
        M.informationMass (sequence n).strategy who site :=
    (approximates n).2 who site ((approximates n).1.informationMass_pos who site) history
  have beliefs : Tendsto (fun n => ((sequence n).belief who site).prob history) atTop
      (nhds (M.historyReachProbability assessment.strategy history.1 /
        M.informationMass assessment.strategy who site)) :=
    ratios.congr' (Filter.Eventually.of_forall fun n => (equality n).symm)
  exact tendsto_nhds_unique (converges.belief who site history) beliefs

variable [DecidableEq ι]

theorem BehavioralAssessmentConvergesPointwise.context_value
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    {who : ι} (site : M.InformationSite who)
    [Finite (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (alternatives : ℕ → M.BehavioralPolicy who) (alternative : M.BehavioralPolicy who)
    (alternativesConverge : ∀ decision : M.InformationSite who,
      FinDistConvergesPointwise (fun n => alternatives n decision.1) (alternative decision.1)) :
    Tendsto (fun n => ((sequence n).continuationContext site payoff fuel).value
      (alternatives n)) atTop
      (nhds ((assessment.continuationContext site payoff fuel).value alternative)) := by
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  apply (converges.belief who site).expect_varying
  intro history
  apply runBehavioralFrom_expect_tendsto reference mixed
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
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    {sequence : ℕ → M.BehavioralAssessment} {assessment : M.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    {who : ι} (site : M.InformationSite who)
    [Finite (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (responses : ℕ → M.BehavioralPolicy who)
    (responsesConverge : ∀ decision : M.InformationSite who,
      FinDistConvergesPointwise (fun n => responses n decision.1)
        (assessment.strategy who decision.1))
    (optimal : ∀ n alternative,
      ((sequence n).continuationContext site payoff fuel).value alternative ≤
        ((sequence n).continuationContext site payoff fuel).value (responses n)) :
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext site payoff fuel) := by
  intro alternative _
  exact le_of_tendsto_of_tendsto
    (converges.context_value reference mixed site payoff fuel (fun _ => alternative) alternative
      (fun _ => finDistConvergesPointwise_const _))
    (converges.context_value reference mixed site payoff fuel responses (assessment.strategy who)
      responsesConverge)
    (Filter.Eventually.of_forall (fun n => optimal n alternative))

end GameTheory.Protocol.InformationModel
