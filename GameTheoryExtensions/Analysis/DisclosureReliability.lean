/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.FinitePayoffBounds

/-! # Reliability comparisons for a disclosure phase

A successful disclosure has one continuation payoff, and an unsuccessful
disclosure has another, minus a fixed forfeit. Bounded continuation payoffs give
robust comparisons against protected execution and against never disclosing.
When the two continuation payoffs do not change with timing, every hidden type
ranks timings by inclusion probability. For finitely many attainable inclusion
probabilities, one finite forfeit ranks distinct probabilities uniformly even
when the bounded continuation values vary with timing and hidden type.

These are phase comparison lemmas. They do not construct a runtime assessment,
transport beliefs, identify continuation values of an asynchronous service, or
resolve ties between equally reliable timing options.
-/

noncomputable section

namespace GameTheory.DisclosureReliability

/-- Expected payoff of a disclosure whose unsuccessful branch incurs a forfeit. -/
def value (probability success failure forfeit : ℝ) : ℝ :=
  probability * success + (1 - probability) * (failure - forfeit)

theorem value_eq_base_minus_forfeit (probability success failure forfeit : ℝ) :
    value probability success failure forfeit =
      value probability success failure 0 - (1 - probability) * forfeit := by
  unfold value
  ring

theorem value_upper (probability success failure forfeit upper : ℝ)
    (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (success_upper : success ≤ upper) (failure_upper : failure ≤ upper) :
    value probability success failure forfeit ≤ upper - (1 - probability) * forfeit := by
  have first := mul_le_mul_of_nonneg_left success_upper nonnegative
  have second := mul_le_mul_of_nonneg_left failure_upper (by linarith : 0 ≤ 1 - probability)
  unfold value
  nlinarith

theorem value_lower (probability success failure forfeit lower : ℝ)
    (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (success_lower : lower ≤ success) (failure_lower : lower ≤ failure) :
    lower - (1 - probability) * forfeit ≤ value probability success failure forfeit := by
  have first := mul_le_mul_of_nonneg_left success_lower nonnegative
  have second := mul_le_mul_of_nonneg_left failure_lower (by linarith : 0 ≤ 1 - probability)
  unfold value
  nlinarith

/-- A sufficiently large expected failure cost bounds every late payoff by a
protected lower bound, independently of the prescribed continuation replies. -/
theorem not_profitable_of_failure_cost
    (probability success failure forfeit lower upper protectedValue : ℝ)
    (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (success_upper : success ≤ upper) (failure_upper : failure ≤ upper)
    (protected_lower : lower ≤ protectedValue)
    (failure_cost : upper - lower ≤ (1 - probability) * forfeit) :
    value probability success failure forfeit ≤ protectedValue := by
  have bound := value_upper probability success failure forfeit upper nonnegative bounded
    success_upper failure_upper
  linarith

/-- Sending instead of never disclosing gains at least probability times the
forfeit, minus the complete base-payoff range. -/
theorem send_gain_lower
    (probability success failure never forfeit lower upper : ℝ)
    (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (success_lower : lower ≤ success) (failure_lower : lower ≤ failure)
    (never_upper : never ≤ upper) :
    probability * forfeit - (upper - lower) ≤
      value probability success failure forfeit - (never - forfeit) := by
  have bound := value_lower probability success failure forfeit lower nonnegative bounded
    success_lower failure_lower
  nlinarith

theorem send_strict_of_probability_forfeit
    (probability success failure never forfeit lower upper : ℝ)
    (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (success_lower : lower ≤ success) (failure_lower : lower ≤ failure)
    (never_upper : never ≤ upper)
    (margin : upper - lower < probability * forfeit) :
    never - forfeit < value probability success failure forfeit := by
  have bound := send_gain_lower probability success failure never forfeit lower upper
    nonnegative bounded success_lower failure_lower never_upper
  linarith

/-- If the forfeit exceeds twice the base range, every potentially profitable
late send is strictly preferable to never sending, for every hidden type. -/
theorem send_strict_of_profitable_delay
    (probability success failure never forfeit lower upper protectedValue : ℝ)
    (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (success_lower : lower ≤ success) (failure_lower : lower ≤ failure)
    (success_upper : success ≤ upper) (failure_upper : failure ≤ upper)
    (never_upper : never ≤ upper) (protected_lower : lower ≤ protectedValue)
    (large : 2 * (upper - lower) < forfeit)
    (profitable : protectedValue < value probability success failure forfeit) :
    never - forfeit < value probability success failure forfeit := by
  have upperBound := value_upper probability success failure forfeit upper
    nonnegative bounded success_upper failure_upper
  have margin : upper - lower < probability * forfeit := by nlinarith
  exact send_strict_of_probability_forfeit probability success failure never forfeit lower upper
    nonnegative bounded success_lower failure_lower never_upper margin

theorem reliability_gain_eq (first second success failure forfeit : ℝ) :
    value second success failure forfeit - value first success failure forfeit =
      (second - first) * (success - failure + forfeit) := by
  unfold value
  ring

/-- With timing-independent continuation values, a forfeit larger than the
base range makes reliability and payoff have exactly the same strict order. -/
theorem value_lt_iff_probability_lt (first second success failure forfeit lower upper : ℝ)
    (success_lower : lower ≤ success) (failure_upper : failure ≤ upper)
    (large : upper - lower < forfeit) :
    value first success failure forfeit < value second success failure forfeit ↔
      first < second := by
  have positive : 0 < success - failure + forfeit := by linarith
  rw [← sub_pos, reliability_gain_eq]
  constructor
  · intro better
    have diff : 0 < second - first := (mul_pos_iff_of_pos_right positive).mp better
    linarith
  · intro reliable
    exact mul_pos (sub_pos.mpr reliable) positive

/-- A finite reliability carrier has a positive gap between every two distinct
ordered probabilities. No positive lower bound on the probabilities is assumed. -/
theorem exists_positive_gap {Choice : Type*} [Finite Choice] (probability : Choice → ℝ) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ first second, probability first < probability second →
      gap ≤ probability second - probability first := by
  classical
  let Pair := {pair : Choice × Choice // probability pair.1 < probability pair.2}
  by_cases increasing : ∃ first second, probability first < probability second
  · obtain ⟨first, second, better⟩ := increasing
    let : Nonempty Pair := ⟨⟨(first, second), better⟩⟩
    let : Fintype Pair := Fintype.ofFinite Pair
    let difference : Pair → ℝ := fun pair => probability pair.val.2 - probability pair.val.1
    refine ⟨FinitePayoffBounds.lower difference, ?_, ?_⟩
    · exact (FinitePayoffBounds.lt_lower_iff difference 0).mpr fun pair =>
        sub_pos.mpr pair.property
    · intro first second better
      exact FinitePayoffBounds.lower_le difference ⟨(first, second), better⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro first second better
    exact (increasing ⟨first, second, better⟩).elim

/-- Unequal reliability dominates arbitrary bounded differences in the two
continuation values once its probability gap times the forfeit exceeds the
complete base range. -/
theorem value_lt_of_probability_gap
    (first second firstSuccess secondSuccess firstFailure secondFailure
      forfeit lower upper gap : ℝ)
    (first_nonnegative : 0 ≤ first) (first_bounded : first ≤ 1)
    (second_nonnegative : 0 ≤ second) (second_bounded : second ≤ 1)
    (first_success_upper : firstSuccess ≤ upper)
    (first_failure_upper : firstFailure ≤ upper)
    (second_success_lower : lower ≤ secondSuccess)
    (second_failure_lower : lower ≤ secondFailure)
    (forfeit_nonnegative : 0 ≤ forfeit) (separated : gap ≤ second - first)
    (margin : upper - lower < gap * forfeit) :
    value first firstSuccess firstFailure forfeit <
      value second secondSuccess secondFailure forfeit := by
  have firstBound := value_upper first firstSuccess firstFailure forfeit upper
    first_nonnegative first_bounded first_success_upper first_failure_upper
  have secondBound := value_lower second secondSuccess secondFailure forfeit lower
    second_nonnegative second_bounded second_success_lower second_failure_lower
  have gapBound := mul_le_mul_of_nonneg_right separated forfeit_nonnegative
  nlinarith

/-- One finite forfeit ranks every pair of distinct attainable reliabilities,
uniformly over arbitrary hidden types and bounded continuation values. The
conclusion deliberately makes no comparison between equal probabilities. -/
theorem exists_uniform_reliability_forfeit {Choice Hidden : Type*} [Finite Choice]
    (probability : Choice → ℝ) (success failure : Hidden → Choice → ℝ)
    (lower upper : ℝ) (ordered : lower ≤ upper)
    (nonnegative : ∀ choice, 0 ≤ probability choice)
    (bounded : ∀ choice, probability choice ≤ 1)
    (within : ∀ hidden choice,
      lower ≤ success hidden choice ∧ success hidden choice ≤ upper ∧
        lower ≤ failure hidden choice ∧ failure hidden choice ≤ upper) :
    ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ forfeit, cutoff ≤ forfeit →
      ∀ hidden first second, probability first < probability second →
        value (probability first) (success hidden first) (failure hidden first) forfeit <
          value (probability second) (success hidden second) (failure hidden second) forfeit := by
  obtain ⟨gap, positive, separated⟩ := exists_positive_gap probability
  let cutoff := (upper - lower) / gap + 1
  have ratio_nonnegative : 0 ≤ (upper - lower) / gap := div_nonneg (sub_nonneg.mpr ordered)
    positive.le
  have cutoff_nonnegative : 0 ≤ cutoff := by dsimp [cutoff]; linarith
  refine ⟨cutoff, cutoff_nonnegative, ?_⟩
  intro forfeit sufficient hidden first second better
  have forfeit_nonnegative : 0 ≤ forfeit := cutoff_nonnegative.trans sufficient
  have margin : upper - lower < gap * forfeit := by
    have scaled := mul_le_mul_of_nonneg_left sufficient positive.le
    have cancellation : gap * ((upper - lower) / gap) = upper - lower := by
      field_simp [positive.ne']
    dsimp [cutoff] at scaled
    rw [mul_add, cancellation, mul_one] at scaled
    linarith
  exact value_lt_of_probability_gap _ _ _ _ _ _ _ lower upper gap
    (nonnegative first) (bounded first) (nonnegative second) (bounded second)
    (within hidden first).2.1 (within hidden first).2.2.2
    (within hidden second).1 (within hidden second).2.2.1
    forfeit_nonnegative (separated first second better) margin

end GameTheory.DisclosureReliability
