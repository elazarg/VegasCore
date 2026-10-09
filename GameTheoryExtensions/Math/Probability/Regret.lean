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

end GameTheory.Math.Probability
