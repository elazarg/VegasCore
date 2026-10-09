/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Expectation

/-! # Averaging conditional regret bounds

A pointwise comparator at every history gives an expected regret bound under
any belief. The error event is measured under the compared continuation law;
no Bayes consistency or positive observation mass is needed for this averaging
step. Strategic and informational applicability remain separate hypotheses.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Classical in
/-- Average a pointwise improvement and failure gap over arbitrary beliefs
and continuation kernels. The kernels need not share a state space. -/
theorem expect_failure_regret {History Raw Comparator : Type*}
    (belief : PMF History) (raw : History → PMF Raw) (comparator : History → PMF Comparator)
    (rawPayoff : Raw → ℝ) (comparatorPayoff : Comparator → ℝ)
    (failure : Set Raw) (gap : ℝ)
    (rawIntegrable : PayoffIntegrable (belief.bind raw) rawPayoff)
    (comparatorIntegrable : PayoffIntegrable (belief.bind comparator) comparatorPayoff)
    (rawBranches : ∀ history ∈ belief.support, PayoffIntegrable (raw history) rawPayoff)
    (comparatorBranches : ∀ history ∈ belief.support,
      PayoffIntegrable (comparator history) comparatorPayoff)
    (dominates : ∀ history ∈ belief.support,
      ∀ first ∈ (raw history).support, ∀ second ∈ (comparator history).support,
        rawPayoff first + gap * (if first ∈ failure then 1 else 0) ≤ comparatorPayoff second) :
    gap * ((belief.bind raw).toOuterMeasure failure).toReal ≤
      expect (belief.bind comparator) comparatorPayoff - expect (belief.bind raw) rawPayoff := by
  let augmented : Raw → ℝ := fun first =>
    rawPayoff first + gap * if first ∈ failure then 1 else 0
  have integrableAugmented : PayoffIntegrable (belief.bind raw) augmented :=
    payoffIntegrable_add rawIntegrable
      (payoffIntegrable_const_mul (payoffIntegrable_ite_one_zero _ (· ∈ failure)))
  have branch : ∀ history ∈ belief.support,
      expect (raw history) augmented ≤ expect (comparator history) comparatorPayoff := by
    intro history supported
    have augmentedBranch : PayoffIntegrable (raw history) augmented :=
      payoffIntegrable_add (rawBranches history supported)
        (payoffIntegrable_const_mul (payoffIntegrable_ite_one_zero _ (· ∈ failure)))
    apply expect_le_const _ augmented augmentedBranch
      (expect (comparator history) comparatorPayoff)
    intro first reached
    have averaged := expect_mono (dominates history supported first reached)
      (payoffIntegrable_constant (comparator history) (augmented first))
      (comparatorBranches history supported)
    simpa only [expect_constant] using averaged
  have total := expect_mono branch
    (payoffIntegrable_bind_conditionalExpectation belief raw augmented integrableAugmented)
    (payoffIntegrable_bind_conditionalExpectation belief comparator comparatorPayoff
      comparatorIntegrable)
  rw [← expect_bind_tower belief raw augmented integrableAugmented,
    ← expect_bind_tower belief comparator comparatorPayoff comparatorIntegrable] at total
  have indicatorIntegrable : PayoffIntegrable (belief.bind raw)
      (fun first => if first ∈ failure then (1 : ℝ) else 0) := payoffIntegrable_ite_one_zero _ _
  have expanded : expect (belief.bind raw) augmented = expect (belief.bind raw) rawPayoff +
      gap * ((belief.bind raw).toOuterMeasure failure).toReal := by
    change expect (belief.bind raw)
      (fun first => rawPayoff first + gap * if first ∈ failure then 1 else 0) = _
    rw [expect_add rawIntegrable (payoffIntegrable_const_mul indicatorIntegrable), expect_const_mul]
    exact congrArg (fun mass => expect (belief.bind raw) rawPayoff + gap * mass)
      (expect_indicator (belief.bind raw) failure)
  rw [expanded] at total
  linarith

open Classical in
/-- Two actual deviation comparisons can eliminate costly responses even
when silence with the incumbent future policy is not pointwise optimal.
One comparison bounds that silence value; the other bounds the incumbent
loss relative to an attainable outside value of zero. -/
theorem eventProbability_le_of_two_value_comparisons {Action : Type*}
    (law : PMF Action) (payoff : Action → ℝ) (costly : Set Action)
    (quiet gap quietError outsideError : ℝ)
    (integrable : PayoffIntegrable law payoff)
    (costlyBound : ∀ action ∈ law.support, action ∈ costly → payoff action ≤ -gap)
    (quietBound : ∀ action ∈ law.support, action ∉ costly → payoff action ≤ quiet)
    (quietComparison : quiet - expect law payoff ≤ quietError)
    (outsideComparison : -expect law payoff ≤ outsideError)
    (positive : 0 < gap + quietError - outsideError) :
    (law.toOuterMeasure costly).toReal ≤ quietError / (gap + quietError - outsideError) := by
  let mass := (law.toOuterMeasure costly).toReal
  have massNonnegative : 0 ≤ mass := ENNReal.toReal_nonneg
  have massAtMostOne : mass ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using outerMeasure_le_one law costly)
  let ceiling := fun action => quiet + (-gap - quiet) *
    if action ∈ costly then (1 : ℝ) else 0
  have indicatorIntegrable : PayoffIntegrable law
      (fun action => if action ∈ costly then (1 : ℝ) else 0) :=
    payoffIntegrable_ite_one_zero law (· ∈ costly)
  have ceilingIntegrable : PayoffIntegrable law ceiling :=
    payoffIntegrable_add (payoffIntegrable_constant law quiet)
      (payoffIntegrable_const_mul indicatorIntegrable)
  have below : expect law payoff ≤ expect law ceiling := by
    apply expect_mono _ integrable ceilingIntegrable
    intro action reached
    by_cases included : action ∈ costly
    · simp only [ceiling, included, ↓reduceIte, mul_one]
      linarith [costlyBound action reached included]
    · simpa only [ceiling, included, ↓reduceIte, mul_zero, add_zero] using
        quietBound action reached included
  have ceilingValue : expect law ceiling = (1 - mass) * quiet - mass * gap := by
    change expect law (fun action => quiet + (-gap - quiet) *
      if action ∈ costly then (1 : ℝ) else 0) = _
    rw [expect_add (payoffIntegrable_constant law quiet)
      (payoffIntegrable_const_mul indicatorIntegrable), expect_constant,
      expect_const_mul, expect_indicator]
    dsimp only [mass]
    ring
  rw [ceilingValue] at below
  have retained := mul_le_mul_of_nonneg_left quietComparison
    (sub_nonneg.mpr massAtMostOne)
  have outside := mul_le_mul_of_nonneg_left outsideComparison massNonnegative
  apply (le_div_iff₀ positive).mpr
  dsimp only [mass] at *
  nlinarith

open Classical in
/-- Exact comparisons with silence and an attainable nonnegative value force
zero costly-response probability under a strictly positive loss gap. -/
theorem eventProbability_zero_of_two_value_comparisons {Action : Type*}
    (law : PMF Action) (payoff : Action → ℝ) (costly : Set Action) (quiet gap : ℝ)
    (integrable : PayoffIntegrable law payoff)
    (costlyBound : ∀ action ∈ law.support, action ∈ costly → payoff action ≤ -gap)
    (quietBound : ∀ action ∈ law.support, action ∉ costly → payoff action ≤ quiet)
    (quietComparison : quiet ≤ expect law payoff)
    (outsideComparison : 0 ≤ expect law payoff) (positive : 0 < gap) :
    (law.toOuterMeasure costly).toReal = 0 := by
  have bound := eventProbability_le_of_two_value_comparisons law payoff costly quiet gap 0 0
    integrable costlyBound quietBound (by linarith) (by linarith) (by simpa)
  simp only [zero_div] at bound
  exact le_antisymm bound ENNReal.toReal_nonneg

end GameTheory.Math.Probability
