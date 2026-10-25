/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.ExpectationContraction

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
  have failureIntegrable := payoffIntegrable_of_bounded law failure failureBounded
  have lumpedIntegrable := payoffIntegrable_of_bounded law
    (fun h => lumped (record h)) (fun h => lumpedBounded (record h))
  have deviationBounded (h : H) : |failure h - lumped (record h)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [failureBounded h, lumpedBounded (record h)])
  have deviationIntegrable : PayoffIntegrable law
      (fun h => |failure h - lumped (record h)|) :=
    payoffIntegrable_of_bounded law _ (fun h => by
      simpa only [abs_abs] using deviationBounded h)
  have productIntegrable (test : H → ℝ) (bounded : ∀ h, |test h| ≤ 1) :
      PayoffIntegrable law (fun h => (1 - test h) * value h) :=
    payoffIntegrable_of_bounded law _ (C := 2 * bound) fun h => by
      rw [abs_mul]
      have factor : |1 - test h| ≤ 2 := by
        have := abs_sub 1 (test h)
        norm_num at this
        linarith [bounded h]
      exact mul_le_mul factor (valueBounded' h) (abs_nonneg _) (by norm_num)
  have firstProduct := productIntegrable failure failureBounded
  have secondProduct := productIntegrable (fun h => lumped (record h))
    (fun h => lumpedBounded (record h))
  have firstError : |expect law (fun h => (1 - failure h) * value h) -
      expect law (fun h => (1 - lumped (record h)) * value h)| ≤ bound * ε := by
    have pointwise (h : H) :
        |(1 - failure h) * value h - (1 - lumped (record h)) * value h| ≤
          bound * |failure h - lumped (record h)| := by
      rw [show (1 - failure h) * value h - (1 - lumped (record h)) * value h =
        -(value h * (failure h - lumped (record h))) by ring, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_right (valueBounded' h) (abs_nonneg _)
    have absoluteIntegrable : PayoffIntegrable law
        (fun h => |(1 - failure h) * value h - (1 - lumped (record h)) * value h|) := by
      simpa only [PayoffIntegrable, abs_abs] using
        payoffIntegrable_sub firstProduct secondProduct
    calc
      _ ≤ expect law (fun h =>
          |(1 - failure h) * value h - (1 - lumped (record h)) * value h|) :=
        abs_expect_sub_le_expect_abs_sub law _ _ firstProduct secondProduct
      _ ≤ expect law (fun h => bound * |failure h - lumped (record h)|) :=
        expect_mono (fun h _ => pointwise h) absoluteIntegrable
          (payoffIntegrable_const_mul deviationIntegrable)
      _ = bound * expect law (fun h => |failure h - lumped (record h)|) := expect_const_mul
      _ ≤ bound * ε := mul_le_mul_of_nonneg_left near boundNonneg
  have meanError : |expect law failure - expect law (fun h => lumped (record h))| ≤ ε :=
    (abs_expect_sub_le_expect_abs_sub law _ _ failureIntegrable lumpedIntegrable).trans near
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
