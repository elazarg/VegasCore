/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ExpectationComposition
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Decorrelation of a lumped failure from a bounded value

Let a failure probability be within `ε`, in mean, of a function of a record,
and let a value be bounded by `bound`. When the lumped success probability and
the value are uncorrelated up to `γ`, the expectation of the success
probability times the value is within twice the bound times `ε`, plus `γ`, of
the product of their expectations
(`GameTheory.Math.Probability.abs_expect_mul_sub_le_of_uncorrelated`).

A law decorrelates a record and a hidden part up to `γ` when every pair of
unit-bounded functions of them has covariance at most `γ`
(`GameTheory.Math.Probability.BeliefDecorrelated`). For a value read off the
hidden part, the error then grows by twice the bound times `γ`
(`GameTheory.Math.Probability.abs_expect_mul_sub_le_of_decorrelated`).
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- **Decorrelation through a lumped failure.** Let `failure` be within `ε`, in
mean absolute deviation, of a function of a record bounded by one, let `value`
be bounded by `bound`, and let the lumped success probability and the value be
uncorrelated up to `γ`. Then the expected success probability times the value
is within twice the bound times `ε` plus `γ` of the expected success
probability times the expected value. -/
theorem abs_expect_mul_sub_le_of_uncorrelated {H R : Type*} (law : PMF H) (record : H → R)
    (failure value : H → ℝ) (lumped : R → ℝ) {bound ε γ : ℝ}
    (failureBounded : ∀ h, |failure h| ≤ 1) (lumpedBounded : ∀ ρ, |lumped ρ| ≤ 1)
    (valueBounded' : ∀ h, |value h| ≤ bound)
    (near : expect law (fun h => |failure h - lumped (record h)|) ≤ ε)
    (uncorrelated : |expect law (fun h => (1 - lumped (record h)) * value h) -
      (1 - expect law (fun h => lumped (record h))) * expect law value| ≤ γ) :
    |expect law (fun h => (1 - failure h) * value h) -
      (1 - expect law failure) * expect law value| ≤ 2 * bound * ε + γ := by
  have boundNonneg : 0 ≤ bound := by
    obtain ⟨witness, _⟩ := law.support_nonempty
    exact (abs_nonneg _).trans (valueBounded' witness)
  have twoBound : ∀ x : ℝ, |x| ≤ 1 → |1 - x| ≤ 2 := fun x bounded => by
    rw [abs_le] at bounded ⊢
    constructor <;> linarith
  have deviationIntegrable : PayoffIntegrable law fun h => |failure h - lumped (record h)| :=
    payoffIntegrable_of_bounded _ _ (C := 2) fun h => by
      rw [abs_abs]
      calc |failure h - lumped (record h)| ≤ |failure h| + |lumped (record h)| := abs_sub _ _
        _ ≤ 2 := by linarith [failureBounded h, lumpedBounded (record h)]
  have integrable : ∀ f : H → ℝ, ∀ C, (∀ h, |f h| ≤ C) → PayoffIntegrable law f :=
    fun f C bounded => payoffIntegrable_of_bounded _ _ bounded
  have failureIntegrable := integrable failure 1 failureBounded
  have lumpedIntegrable := integrable (fun h => lumped (record h)) 1 fun h => lumpedBounded _
  have valueIntegrable := integrable value bound valueBounded'
  -- The first error: replacing the failure by its lumped value under the value.
  have firstError : |expect law (fun h => (1 - failure h) * value h) -
      expect law (fun h => (1 - lumped (record h)) * value h)| ≤ bound * ε := by
    rw [← expect_sub (integrable _ (2 * bound) fun h => by
        rw [abs_mul]
        exact mul_le_mul (twoBound _ (failureBounded h)) (valueBounded' h) (abs_nonneg _)
          (by norm_num))
      (integrable _ (2 * bound) fun h => by
        rw [abs_mul]
        exact mul_le_mul (twoBound _ (lumpedBounded _)) (valueBounded' h) (abs_nonneg _)
          (by norm_num))]
    have pointwise : ∀ h, |(1 - failure h) * value h - (1 - lumped (record h)) * value h| ≤
        bound * |failure h - lumped (record h)| := fun h => by
      rw [show (1 - failure h) * value h - (1 - lumped (record h)) * value h =
        -(value h * (failure h - lumped (record h))) by ring, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_right (valueBounded' h) (abs_nonneg _)
    calc _ ≤ expect law (fun h => bound * |failure h - lumped (record h)|) := by
          refine abs_le.mpr ⟨?_, ?_⟩
          · have lower := expect_mono (μ := law)
              (f := fun h => -(bound * |failure h - lumped (record h)|))
              (g := fun h => (1 - failure h) * value h - (1 - lumped (record h)) * value h)
              (fun h _ => neg_le_of_abs_le (pointwise h))
              (integrable _ (bound * 2) fun h => by
                rw [abs_neg, abs_mul, abs_of_nonneg boundNonneg, abs_abs]
                exact mul_le_mul_of_nonneg_left (by
                  calc |failure h - lumped (record h)| ≤ |failure h| + |lumped (record h)| :=
                        abs_sub _ _
                    _ ≤ 2 := by linarith [failureBounded h, lumpedBounded (record h)])
                  boundNonneg)
              (integrable _ (4 * bound) fun h => (pointwise h).trans (by
                calc bound * |failure h - lumped (record h)| ≤ bound * 2 :=
                      mul_le_mul_of_nonneg_left (by
                        calc |failure h - lumped (record h)| ≤
                              |failure h| + |lumped (record h)| := abs_sub _ _
                          _ ≤ 2 := by linarith [failureBounded h, lumpedBounded (record h)])
                        boundNonneg
                  _ ≤ 4 * bound := by linarith))
            rw [expect_neg] at lower
            linarith
          · exact expect_mono (fun h _ => le_of_abs_le (pointwise h))
              (integrable _ (4 * bound) fun h => (pointwise h).trans (by
                calc bound * |failure h - lumped (record h)| ≤ bound * 2 :=
                      mul_le_mul_of_nonneg_left (by
                        calc |failure h - lumped (record h)| ≤
                              |failure h| + |lumped (record h)| := abs_sub _ _
                          _ ≤ 2 := by linarith [failureBounded h, lumpedBounded (record h)])
                        boundNonneg
                  _ ≤ 4 * bound := by linarith))
              (integrable _ (bound * 2) fun h => by
                rw [abs_mul, abs_of_nonneg boundNonneg, abs_abs]
                exact mul_le_mul_of_nonneg_left (by
                  calc |failure h - lumped (record h)| ≤ |failure h| + |lumped (record h)| :=
                        abs_sub _ _
                    _ ≤ 2 := by linarith [failureBounded h, lumpedBounded (record h)])
                  boundNonneg)
      _ = bound * expect law (fun h => |failure h - lumped (record h)|) := expect_const_mul
      _ ≤ bound * ε := mul_le_mul_of_nonneg_left near boundNonneg
  -- The second error: the expected failure against its lumped mean.
  have meanError : |expect law failure - expect law (fun h => lumped (record h))| ≤ ε := by
    rw [← expect_sub failureIntegrable lumpedIntegrable]
    refine le_trans ?_ near
    refine abs_le.mpr ⟨?_, ?_⟩
    · have lower := expect_mono (μ := law) (f := fun h => -|failure h - lumped (record h)|)
        (g := fun h => failure h - lumped (record h)) (fun h _ => neg_abs_le _)
        (integrable _ 2 fun h => by
          rw [abs_neg, abs_abs]
          calc |failure h - lumped (record h)| ≤ |failure h| + |lumped (record h)| := abs_sub _ _
            _ ≤ 2 := by linarith [failureBounded h, lumpedBounded (record h)])
        (payoffIntegrable_sub failureIntegrable lumpedIntegrable)
      rw [expect_neg] at lower
      linarith
    · exact expect_mono (fun h _ => le_abs_self _)
        (payoffIntegrable_sub failureIntegrable lumpedIntegrable) deviationIntegrable
  have valueMean : |expect law value| ≤ bound := expect_abs_le_of_bounded boundNonneg valueBounded'
  calc _ = |(expect law (fun h => (1 - failure h) * value h) -
          expect law (fun h => (1 - lumped (record h)) * value h)) +
        (expect law failure - expect law (fun h => lumped (record h))) * expect law value +
        (expect law (fun h => (1 - lumped (record h)) * value h) -
          (1 - expect law (fun h => lumped (record h))) * expect law value)| := by
        congr 1
        ring
    _ ≤ |expect law (fun h => (1 - failure h) * value h) -
          expect law (fun h => (1 - lumped (record h)) * value h)| +
        |expect law failure - expect law (fun h => lumped (record h))| *
          |expect law value| + γ := by
        rw [← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) uncorrelated)
    _ ≤ bound * ε + ε * bound + γ := by
        exact add_le_add (add_le_add firstError (mul_le_mul meanError valueMean (abs_nonneg _)
          ((abs_nonneg _).trans meanError))) le_rfl
    _ = 2 * bound * ε + γ := by ring


/-- **A decorrelated record and hidden part.** Under `law`, every function of
the record and every function of the hidden part, both bounded by one, have the
expectation of their product within `γ` of the product of their expectations. -/
def BeliefDecorrelated {H R T : Type*} (law : PMF H) (record : H → R) (hidden : H → T)
    (γ : ℝ) : Prop :=
  ∀ (first : R → ℝ) (second : T → ℝ), (∀ ρ, |first ρ| ≤ 1) → (∀ τ, |second τ| ≤ 1) →
    |expect law (fun h => first (record h) * second (hidden h)) -
      expect law (fun h => first (record h)) * expect law (fun h => second (hidden h))| ≤ γ

/-- Decorrelation up to an error holds up to every larger error. -/
theorem BeliefDecorrelated.mono {H R T : Type*} {law : PMF H} {record : H → R}
    {hidden : H → T} {γ γ' : ℝ} (decorrelated : BeliefDecorrelated law record hidden γ)
    (le : γ ≤ γ') : BeliefDecorrelated law record hidden γ' :=
  fun first second firstBounded secondBounded =>
    (decorrelated first second firstBounded secondBounded).trans le

/-- **Decorrelation up to a covariance bound.** Let a law decorrelate a record
and a hidden part up to `γ`. Let `failure` be within `ε`, in mean absolute
deviation, of a function of the record bounded by one, and let `value` be a
function of the hidden part bounded by `bound`. Then the expected success
probability times the value is within twice the bound times `ε + γ` of the
expected success probability times the expected value. -/
theorem abs_expect_mul_sub_le_of_decorrelated {H R T : Type*} (law : PMF H) (record : H → R)
    (hidden : H → T) {γ : ℝ} (decorrelated : BeliefDecorrelated law record hidden γ)
    (failure value : H → ℝ) (lumped : R → ℝ) (valueOf : T → ℝ) {bound ε : ℝ}
    (failureBounded : ∀ h, |failure h| ≤ 1) (lumpedBounded : ∀ ρ, |lumped ρ| ≤ 1)
    (valueBounded : ∀ τ, |valueOf τ| ≤ bound) (valueEq : ∀ h, value h = valueOf (hidden h))
    (near : expect law (fun h => |failure h - lumped (record h)|) ≤ ε) :
    |expect law (fun h => (1 - failure h) * value h) -
      (1 - expect law failure) * expect law value| ≤ 2 * bound * ε + 2 * bound * γ := by
  have valueBounded' : ∀ h, |value h| ≤ bound := fun h => by
    rw [valueEq]
    exact valueBounded _
  obtain ⟨witness, _⟩ := law.support_nonempty
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (valueBounded' witness)
  have lumpedMean : expect law (fun h => 1 - lumped (record h)) =
      1 - expect law (fun h => lumped (record h)) := by
    rw [expect_sub (payoffIntegrable_constant _ 1)
      (payoffIntegrable_of_bounded _ _ fun h => lumpedBounded (record h)), expect_constant]
  have uncorrelated : |expect law (fun h => (1 - lumped (record h)) * value h) -
      (1 - expect law (fun h => lumped (record h))) * expect law value| ≤ 2 * bound * γ := by
    rcases boundNonneg.lt_or_eq with positive | zero
    · have scaled := decorrelated (fun ρ => (1 - lumped ρ) / 2) (fun τ => valueOf τ / bound)
        (fun ρ => by
          have := abs_le.mp (lumpedBounded ρ)
          rw [abs_le]
          constructor <;> linarith)
        (fun τ => by
          rw [abs_div, abs_of_pos positive, div_le_one positive]
          exact valueBounded τ)
      have productEq : (fun h => (1 - lumped (record h)) / 2 * (valueOf (hidden h) / bound)) =
          fun h => (1 / (2 * bound)) * ((1 - lumped (record h)) * value h) := by
        funext h
        rw [valueEq]
        field_simp
      have firstEq : (fun h => (1 - lumped (record h)) / 2) =
          fun h => (1 / 2) * (1 - lumped (record h)) := by
        funext h
        ring
      have secondEq : (fun h => valueOf (hidden h) / bound) =
          fun h => (1 / bound) * value h := by
        funext h
        rw [valueEq]
        ring
      rw [productEq, firstEq, secondEq, expect_const_mul, expect_const_mul, expect_const_mul,
        lumpedMean] at scaled
      have factor : (1 / (2 * bound)) * expect law (fun h => (1 - lumped (record h)) * value h) -
          (1 / 2 * (1 - expect law (fun h => lumped (record h)))) *
            (1 / bound * expect law value) =
          (1 / (2 * bound)) * (expect law (fun h => (1 - lumped (record h)) * value h) -
            (1 - expect law (fun h => lumped (record h))) * expect law value) := by
        field_simp
      rw [factor, abs_mul, abs_of_pos (by positivity)] at scaled
      have twice : 0 < 2 * bound := by positivity
      rw [one_div, inv_mul_le_iff₀ twice] at scaled
      linarith
    · subst zero
      have valueZero : ∀ h, value h = 0 := fun h => abs_nonpos_iff.mp (valueBounded' h)
      have valueFun : value = fun _ => 0 := funext valueZero
      simp [valueFun, expect_constant]
  exact abs_expect_mul_sub_le_of_uncorrelated law record failure value lumped failureBounded
    lumpedBounded valueBounded' near uncorrelated |>.trans_eq (by ring)

end GameTheory.Math.Probability
