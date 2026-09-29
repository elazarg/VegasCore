/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Analysis.IncentiveCone
import GameTheoryExtensions.Analysis.IncentiveComparison
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Deterrence by probabilistic sanctions

A sanction subtracts a fixed amount of utility on a specified event. For a
comparison with an unsanctioned feasible plan, a gain bound `G` and a detection
probability lower bound `p` give regret at most `G - p * penalty`.

The probability and gain bounds concern the actual compared laws. Applied at
an information set, they are conditional on that assessment's beliefs. No
monitor, evidence, collection mechanism, or sequentially consistent belief
system is constructed here. Sanctions are measured in utility, not currency.

For a randomized alarm observing a finite-support law, the largest detection
probability compatible with zero false positives is exactly the deviating
law's mass outside the lawful support. This concerns the specified observable
law. A compiler preserving all source-compatible strategies needs soundness
for each permitted source strategy, not only one equilibrium profile.
-/

noncomputable section

namespace GameTheory

open Math.Probability

namespace Enforcement

variable {Outcome : Type*}

/-- Pay the fixed utility penalty precisely on the sanction event. -/
def sanctionedUtility (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ) :
    Outcome → ℝ := by
  classical
  exact fun outcome => base outcome - if outcome ∈ sanction then penalty else 0

/-- The sanction is bounded, so it preserves integrability of the base utility. -/
theorem payoffIntegrable_sanctionedUtility {law : PMF Outcome} {base : Outcome → ℝ}
    (integrable : PayoffIntegrable law base) (sanction : Set Outcome) (penalty : ℝ) :
    PayoffIntegrable law (sanctionedUtility base sanction penalty) := by
  classical
  unfold sanctionedUtility
  exact payoffIntegrable_sub integrable
    (payoffIntegrable_of_bounded _ _ (C := |penalty|) fun outcome => by split <;> simp)

theorem expect_sanctionedUtility (law : PMF Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) (penalty : ℝ) (integrable : PayoffIntegrable law base) :
    expect law (sanctionedUtility base sanction penalty) =
      expect law base - (law.toOuterMeasure sanction).toReal * penalty := by
  classical
  unfold sanctionedUtility
  rw [expect_sub integrable
    (payoffIntegrable_of_bounded _ _ (C := |penalty|) fun outcome => by split <;> simp)]
  have amount : (fun outcome => if outcome ∈ sanction then penalty else 0) =
      (fun outcome => penalty * if outcome ∈ sanction then (1 : ℝ) else 0) := by
    funext outcome
    split <;> simp
  rw [amount, expect_const_mul, expect_indicator, mul_comm]

/-- The probability difference, rather than detection alone, is what matters
when the comparison plan may also incur a sanction. -/
theorem regret_eq (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) (penalty : ℝ)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base) :
    expect comparison.alternative (sanctionedUtility base sanction penalty) -
        expect comparison.prescribed (sanctionedUtility base sanction penalty) =
      (expect comparison.alternative base - expect comparison.prescribed base) -
        ((comparison.alternative.toOuterMeasure sanction).toReal -
          (comparison.prescribed.toOuterMeasure sanction).toReal) * penalty := by
  rw [expect_sanctionedUtility _ _ _ _ alternativeIntegrable,
    expect_sanctionedUtility _ _ _ _ prescribedIntegrable]
  ring

/-- Conditional detection and bounded gain give a quantitative deterrence certificate. -/
theorem regret_le (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) {penalty gain probability : ℝ}
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : expect comparison.alternative base - expect comparison.prescribed base ≤ gain)
    (detection : probability ≤ (comparison.alternative.toOuterMeasure sanction).toReal)
    (no_sanction : (comparison.prescribed.toOuterMeasure sanction).toReal = 0) :
    expect comparison.alternative (sanctionedUtility base sanction penalty) -
        expect comparison.prescribed (sanctionedUtility base sanction penalty) ≤
      gain - probability * penalty := by
  rw [regret_eq _ _ _ _ prescribedIntegrable alternativeIntegrable, no_sanction, sub_zero]
  exact sub_le_sub gain_bound (mul_le_mul_of_nonneg_right detection penalty_nonneg)

theorem holds_of_sanction (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) {penalty gain probability : ℝ}
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : expect comparison.alternative base - expect comparison.prescribed base ≤ gain)
    (detection : probability ≤ (comparison.alternative.toOuterMeasure sanction).toReal)
    (no_sanction : (comparison.prescribed.toOuterMeasure sanction).toReal = 0)
    (sufficient : gain ≤ probability * penalty) :
    comparison.Holds (sanctionedUtility base sanction penalty) := by
  have bound := regret_le comparison base sanction prescribedIntegrable alternativeIntegrable
    penalty_nonneg gain_bound detection no_sanction
  exact (IncentiveComparison.holds_iff_of_integrable comparison
    (sanctionedUtility base sanction penalty)
    (payoffIntegrable_sanctionedUtility prescribedIntegrable sanction penalty)
    (payoffIntegrable_sanctionedUtility alternativeIntegrable sanction penalty)).mpr
      (sub_nonpos.mp (bound.trans (sub_nonpos.mpr sufficient)))

theorem strictly_prefers_of_sanction (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) {penalty gain probability : ℝ}
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : expect comparison.alternative base - expect comparison.prescribed base ≤ gain)
    (detection : probability ≤ (comparison.alternative.toOuterMeasure sanction).toReal)
    (no_sanction : (comparison.prescribed.toOuterMeasure sanction).toReal = 0)
    (sufficient : gain < probability * penalty) :
    expect comparison.alternative (sanctionedUtility base sanction penalty) <
      expect comparison.prescribed (sanctionedUtility base sanction penalty) := by
  have bound := regret_le comparison base sanction prescribedIntegrable alternativeIntegrable
    penalty_nonneg gain_bound detection no_sanction
  exact sub_neg.mp (bound.trans_lt (sub_neg.mpr sufficient))

/-- A fixed utility sanction cannot deter every positive rescaling of a
profitable base utility. The sanction term is held fixed: this is not a claim
about rescaling the entire utility function, including its value for money. -/
theorem exists_rescaling_defeating_sanction (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed base)
    (alternativeIntegrable : PayoffIntegrable comparison.alternative base)
    (profitable : expect comparison.prescribed base < expect comparison.alternative base) :
    ∃ scale : ℝ, 0 < scale ∧
      expect comparison.prescribed
          (sanctionedUtility (fun outcome => scale * base outcome) sanction penalty) <
        expect comparison.alternative
          (sanctionedUtility (fun outcome => scale * base outcome) sanction penalty) := by
  let advantage := expect comparison.alternative base - expect comparison.prescribed base
  let charge :=
    ((comparison.alternative.toOuterMeasure sanction).toReal -
      (comparison.prescribed.toOuterMeasure sanction).toReal) * penalty
  have advantage_pos : 0 < advantage := sub_pos.mpr profitable
  let scale := (|charge| + 1) / advantage
  have scale_pos : 0 < scale := div_pos (by positivity) advantage_pos
  refine ⟨scale, scale_pos, sub_pos.mp ?_⟩
  rw [regret_eq _ _ _ _ (payoffIntegrable_const_mul prescribedIntegrable)
      (payoffIntegrable_const_mul alternativeIntegrable), expect_const_mul, expect_const_mul,
    ← mul_sub]
  change 0 < scale * advantage - charge
  dsimp only [scale]
  rw [div_mul_cancel₀ _ advantage_pos.ne']
  linarith [le_abs_self charge]

/-- Zero false positives require the alarm to stay silent at every observation
with positive lawful probability, even when the alarm itself randomizes. -/
theorem alarm_zero_iff (lawful : PMF Outcome) (alarm : Outcome → PMF Bool) :
    ((lawful.bind alarm) true).toReal = 0 ↔
      ∀ outcome ∈ lawful.support, ((alarm outcome) true).toReal = 0 := by
  simp only [pmf_toReal_eq_zero_iff, PMF.mem_support_bind_iff]
  constructor
  · intro silent outcome supported reported
    exact silent ⟨outcome, supported, reported⟩
  · rintro silent ⟨outcome, supported, reported⟩
    exact silent outcome supported reported

/-- A sound alarm can detect only the deviating probability mass outside the
lawful observable support. Randomization does not improve this bound. -/
theorem detection_le_outside_support (lawful deviating : PMF Outcome)
    (alarm : Outcome → PMF Bool)
    (no_false_positives : ((lawful.bind alarm) true).toReal = 0) :
    ((deviating.bind alarm) true).toReal ≤ (deviating.toOuterMeasure lawful.supportᶜ).toReal := by
  classical
  rw [toReal_bind_apply, ← expect_indicator]
  apply expect_mono _
    (payoffIntegrable_of_bounded _ _ (C := 1) fun outcome => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact pmf_toReal_apply_le_one _ _)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun outcome => by split <;> simp)
  intro outcome _
  by_cases supported : outcome ∈ lawful.support
  · rw [(alarm_zero_iff lawful alarm).mp no_false_positives outcome supported]
    simp only [Set.mem_compl_iff, supported, not_true_eq_false, ite_false, le_refl]
  · simp only [Set.mem_compl_iff, supported, not_false_eq_true, ite_true]
    exact pmf_toReal_apply_le_one (alarm outcome) true

/-- The upper bound is attained by one deterministic alarm, simultaneously
for every deviating law. This is an existence statement over the specified
observation carrier, not an implementation of a runtime monitor. -/
theorem exists_optimal_sound_alarm (lawful : PMF Outcome) :
    ∃ alarm : Outcome → PMF Bool,
      ((lawful.bind alarm) true).toReal = 0 ∧
        ∀ deviating : PMF Outcome,
          ((deviating.bind alarm) true).toReal =
            (deviating.toOuterMeasure lawful.supportᶜ).toReal := by
  classical
  let alarm : Outcome → PMF Bool := fun outcome =>
    PMF.pure (decide (outcome ∉ lawful.support))
  refine ⟨alarm, ?_, ?_⟩
  · apply (alarm_zero_iff lawful alarm).mpr
    intro outcome supported
    simp [alarm, (PMF.mem_support_iff _ _).mp supported]
  · intro deviating
    rw [toReal_bind_apply, ← expect_indicator]
    apply expect_congr_on_support
    intro outcome _
    by_cases supported : outcome ∈ lawful.support
    · simp [alarm, supported, (PMF.mem_support_iff _ _).mp supported]
    · simp [alarm, supported, (PMF.apply_eq_zero_iff _ _).mpr supported]

/-- If every deviating observation is also lawful, zero false positives force
zero detection, even when the two observation laws have different probabilities. -/
theorem alarm_zero_of_support_subset (lawful deviating : PMF Outcome)
    (included : deviating.support ⊆ lawful.support) (alarm : Outcome → PMF Bool)
    (no_false_positives : ((lawful.bind alarm) true).toReal = 0) :
    ((deviating.bind alarm) true).toReal = 0 := by
  apply (alarm_zero_iff deviating alarm).mpr
  intro outcome supported
  exact (alarm_zero_iff lawful alarm).mp no_false_positives outcome (included supported)

end Enforcement

namespace Protocol.InformationModel.BehavioralAssessment

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} {M : InformationModel E}

/-- A deterrence certificate for every whole continuation deviation establishes
local sequential rationality in the actual assessment context. Every bound is
at this information set; an initialized detection bound alone does not suffice. -/
theorem isSequentiallyRationalAt_of_sanction
    (assessment : M.BehavioralAssessment) {who : ι} (site : M.InformationSite who)
    (base : E.History → ℝ) (sanction : Set E.History) (fuel : Nat) {penalty : ℝ}
    (penalty_nonneg : 0 ≤ penalty)
    (gain probability : M.BehavioralPolicy who → ℝ)
    (integrable : ∀ policy, (assessment.continuationContext site base fuel).IntegrableAt policy)
    (no_sanction : (((assessment.continuationContext site base fuel).outcome
      (assessment.strategy who)).toOuterMeasure sanction).toReal = 0)
    (gain_bound : ∀ alternative,
      (assessment.continuationContext site base fuel).value alternative -
        (assessment.continuationContext site base fuel).value (assessment.strategy who) ≤
          gain alternative)
    (detection : ∀ alternative, probability alternative ≤
      (((assessment.continuationContext site base fuel).outcome alternative).toOuterMeasure
        sanction).toReal)
    (sufficient : ∀ alternative, gain alternative ≤ probability alternative * penalty) :
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site
        (Enforcement.sanctionedUtility base sanction penalty) fuel) := by
  have sanctioned (policy : M.BehavioralPolicy who) :
      (assessment.continuationContext site
        (Enforcement.sanctionedUtility base sanction penalty) fuel).IntegrableAt policy :=
    Enforcement.payoffIntegrable_sanctionedUtility (integrable policy) sanction penalty
  refine (Context.isLocallyOptimal_iff_of_integrable (sanctioned _)
    fun alternative _ => sanctioned alternative).mpr fun alternative _ => ?_
  let comparison : IncentiveComparison E.History := {
    prescribed := (assessment.continuationContext site base fuel).outcome
      (assessment.strategy who)
    alternative := (assessment.continuationContext site base fuel).outcome alternative }
  exact (IncentiveComparison.holds_iff_of_integrable comparison
    (Enforcement.sanctionedUtility base sanction penalty)
    (Enforcement.payoffIntegrable_sanctionedUtility (integrable (assessment.strategy who))
      sanction penalty)
    (Enforcement.payoffIntegrable_sanctionedUtility (integrable alternative) sanction penalty)).mp
      (Enforcement.holds_of_sanction comparison base sanction
        (integrable (assessment.strategy who)) (integrable alternative)
        penalty_nonneg (gain_bound alternative) (detection alternative) no_sanction
        (sufficient alternative))

end Protocol.InformationModel.BehavioralAssessment
end GameTheory
