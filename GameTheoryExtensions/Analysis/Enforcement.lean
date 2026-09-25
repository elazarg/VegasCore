/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment
import GameTheoryExtensions.Core.IncentiveCone

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

theorem expect_sanctionedUtility (law : FinDist Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) (penalty : ℝ) :
    law.expect (sanctionedUtility base sanction penalty) =
      law.expect base - law.probOf sanction * penalty := by
  classical
  unfold sanctionedUtility
  rw [FinDist.expect_sub]
  have amount : (fun outcome => if outcome ∈ sanction then penalty else 0) =
      (fun outcome => (if outcome ∈ sanction then (1 : ℝ) else 0) * penalty) := by
    funext outcome
    split <;> simp
  rw [amount, FinDist.expect_mul_const, FinDist.expect_indicator_eq_probOf]

/-- The probability difference, rather than detection alone, is what matters
when the comparison plan may also incur a sanction. -/
theorem regret_eq (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) (penalty : ℝ) :
    comparison.alternative.expect (sanctionedUtility base sanction penalty) -
        comparison.prescribed.expect (sanctionedUtility base sanction penalty) =
      (comparison.alternative.expect base - comparison.prescribed.expect base) -
        (comparison.alternative.probOf sanction - comparison.prescribed.probOf sanction) *
          penalty := by
  rw [expect_sanctionedUtility, expect_sanctionedUtility]
  ring

/-- Conditional detection and bounded gain give a quantitative deterrence certificate. -/
theorem regret_le (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) {penalty gain probability : ℝ}
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : comparison.alternative.expect base - comparison.prescribed.expect base ≤ gain)
    (detection : probability ≤ comparison.alternative.probOf sanction)
    (no_sanction : comparison.prescribed.probOf sanction = 0) :
    comparison.alternative.expect (sanctionedUtility base sanction penalty) -
        comparison.prescribed.expect (sanctionedUtility base sanction penalty) ≤
      gain - probability * penalty := by
  rw [regret_eq, no_sanction, sub_zero]
  exact sub_le_sub gain_bound (mul_le_mul_of_nonneg_right detection penalty_nonneg)

theorem holds_of_sanction (comparison : IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome) {penalty gain probability : ℝ}
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : comparison.alternative.expect base - comparison.prescribed.expect base ≤ gain)
    (detection : probability ≤ comparison.alternative.probOf sanction)
    (no_sanction : comparison.prescribed.probOf sanction = 0)
    (sufficient : gain ≤ probability * penalty) :
    comparison.Holds (sanctionedUtility base sanction penalty) := by
  have bound := regret_le comparison base sanction penalty_nonneg gain_bound detection no_sanction
  exact sub_nonpos.mp (bound.trans (sub_nonpos.mpr sufficient))

theorem strictly_prefers_of_sanction (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) {penalty gain probability : ℝ}
    (penalty_nonneg : 0 ≤ penalty)
    (gain_bound : comparison.alternative.expect base - comparison.prescribed.expect base ≤ gain)
    (detection : probability ≤ comparison.alternative.probOf sanction)
    (no_sanction : comparison.prescribed.probOf sanction = 0)
    (sufficient : gain < probability * penalty) :
    comparison.alternative.expect (sanctionedUtility base sanction penalty) <
      comparison.prescribed.expect (sanctionedUtility base sanction penalty) := by
  have bound := regret_le comparison base sanction penalty_nonneg gain_bound detection no_sanction
  exact sub_neg.mp (bound.trans_lt (sub_neg.mpr sufficient))

/-- A fixed utility sanction cannot deter every positive rescaling of a
profitable base utility. The sanction term is held fixed: this is not a claim
about rescaling the entire utility function, including its value for money. -/
theorem exists_rescaling_defeating_sanction (comparison : IncentiveComparison Outcome)
    (base : Outcome → ℝ) (sanction : Set Outcome) (penalty : ℝ)
    (profitable : comparison.prescribed.expect base < comparison.alternative.expect base) :
    ∃ scale : ℝ, 0 < scale ∧
      comparison.prescribed.expect
          (sanctionedUtility (fun outcome => scale * base outcome) sanction penalty) <
        comparison.alternative.expect
          (sanctionedUtility (fun outcome => scale * base outcome) sanction penalty) := by
  let advantage := comparison.alternative.expect base - comparison.prescribed.expect base
  let charge :=
    (comparison.alternative.probOf sanction - comparison.prescribed.probOf sanction) * penalty
  have advantage_pos : 0 < advantage := sub_pos.mpr profitable
  let scale := (|charge| + 1) / advantage
  have scale_pos : 0 < scale := div_pos (by positivity) advantage_pos
  refine ⟨scale, scale_pos, sub_pos.mp ?_⟩
  rw [regret_eq, FinDist.expect_smul, FinDist.expect_smul, ← mul_sub]
  change 0 < scale * advantage - charge
  dsimp only [scale]
  rw [div_mul_cancel₀ _ advantage_pos.ne']
  linarith [le_abs_self charge]

/-- Zero false positives require the alarm to stay silent at every observation
with positive lawful probability, even when the alarm itself randomizes. -/
theorem alarm_zero_iff (lawful : FinDist Outcome) (alarm : Outcome → FinDist Bool) :
    (lawful.bind alarm).prob true = 0 ↔
      ∀ outcome ∈ lawful.support, (alarm outcome).prob true = 0 := by
  constructor
  · intro silent outcome supported
    apply FinDist.prob_eq_zero_iff.mpr
    intro reported
    apply (FinDist.prob_eq_zero_iff.mp silent)
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨outcome, supported, reported⟩
  · intro silent
    apply FinDist.prob_eq_zero_iff.mpr
    intro reported
    simp only [FinDist.support_bind, Set.mem_iUnion] at reported
    obtain ⟨outcome, supported, reported⟩ := reported
    exact (FinDist.prob_eq_zero_iff.mp (silent outcome supported)) reported

/-- A sound alarm can detect only the deviating probability mass outside the
lawful observable support. Randomization does not improve this bound. -/
theorem detection_le_outside_support (lawful deviating : FinDist Outcome)
    (alarm : Outcome → FinDist Bool)
    (no_false_positives : (lawful.bind alarm).prob true = 0) :
    (deviating.bind alarm).prob true ≤ deviating.probOf lawful.supportᶜ := by
  classical
  rw [FinDist.prob_bind, ← FinDist.expect_indicator_eq_probOf]
  apply FinDist.expect_mono
  intro outcome _
  by_cases supported : outcome ∈ lawful.support
  · rw [(alarm_zero_iff lawful alarm).mp no_false_positives outcome supported]
    simp only [Set.mem_compl_iff, supported, not_true_eq_false, ite_false, le_refl]
  · simp only [Set.mem_compl_iff, supported, not_false_eq_true, ite_true]
    exact (alarm outcome).prob_le_one true

/-- The upper bound is attained by one deterministic alarm, simultaneously
for every deviating law. This is an existence statement over the specified
observation carrier, not an implementation of a runtime monitor. -/
theorem exists_optimal_sound_alarm (lawful : FinDist Outcome) :
    ∃ alarm : Outcome → FinDist Bool,
      (lawful.bind alarm).prob true = 0 ∧
        ∀ deviating : FinDist Outcome,
          (deviating.bind alarm).prob true = deviating.probOf lawful.supportᶜ := by
  classical
  let alarm : Outcome → FinDist Bool := fun outcome =>
    FinDist.pure (decide (outcome ∉ lawful.support))
  refine ⟨alarm, ?_, ?_⟩
  · apply (alarm_zero_iff lawful alarm).mpr
    intro outcome supported
    simp [alarm, supported, FinDist.prob_pure_eq_ite]
  · intro deviating
    rw [FinDist.prob_bind, ← FinDist.expect_indicator_eq_probOf]
    apply FinDist.expect_congr
    intro outcome _
    by_cases supported : outcome ∈ lawful.support <;>
      simp [alarm, supported, FinDist.prob_pure_eq_ite]

/-- If every deviating observation is also lawful, zero false positives force
zero detection, even when the two observation laws have different probabilities. -/
theorem alarm_zero_of_support_subset (lawful deviating : FinDist Outcome)
    (included : deviating.support ⊆ lawful.support) (alarm : Outcome → FinDist Bool)
    (no_false_positives : (lawful.bind alarm).prob true = 0) :
    (deviating.bind alarm).prob true = 0 := by
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
    (no_sanction :
      ((assessment.continuationContext site base fuel).outcome (assessment.strategy who)).probOf
        sanction = 0)
    (gain_bound : ∀ alternative,
      (assessment.continuationContext site base fuel).value alternative -
        (assessment.continuationContext site base fuel).value (assessment.strategy who) ≤
          gain alternative)
    (detection : ∀ alternative, probability alternative ≤
      ((assessment.continuationContext site base fuel).outcome alternative).probOf sanction)
    (sufficient : ∀ alternative, gain alternative ≤ probability alternative * penalty) :
    assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site
        (Enforcement.sanctionedUtility base sanction penalty) fuel) := by
  intro alternative _
  let comparison : IncentiveComparison E.History := {
    prescribed := (assessment.continuationContext site base fuel).outcome
      (assessment.strategy who)
    alternative := (assessment.continuationContext site base fuel).outcome alternative }
  exact Enforcement.holds_of_sanction comparison base sanction penalty_nonneg
    (gain_bound alternative) (detection alternative) no_sanction (sufficient alternative)

end Protocol.InformationModel.BehavioralAssessment
end GameTheory
