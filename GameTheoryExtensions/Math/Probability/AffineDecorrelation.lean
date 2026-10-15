/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.ProductDecorrelation

/-! # Affine payoff scores under approximate record independence -/

noncomputable section
namespace GameTheory.Math.Probability

/-- Centering at an exclusion payoff turns a concrete failure/value factor into
an affine scalar score after averaging the actual posterior. -/
theorem abs_expect_affine_sub_le_of_decorrelated
    {H R T : Type*} [Finite H] (law : PMF H) (record : H → R) (hidden : H → T)
    {gamma : ℝ} (decorrelated : BeliefDecorrelated law record hidden gamma)
    (failure payoff value : H → ℝ) (lumped : R → ℝ) (valueOf : T → ℝ)
    (excluded : ℝ) {bound error epsilon : ℝ}
    (failureBounded : ∀ h, |failure h| ≤ 1)
    (lumpedBounded : ∀ record, |lumped record| ≤ 1)
    (valueBounded : ∀ point, |valueOf point| ≤ bound)
    (valueEq : ∀ h, value h = valueOf (hidden h))
    (excludedBounded : |excluded| ≤ bound)
    (failureNear : expect law (fun h => |failure h - lumped (record h)|) ≤ epsilon)
    (payoffNear : expect law (fun h =>
      |payoff h - (excluded + (1 - failure h) * (value h - excluded))|) ≤ error) :
    |expect law payoff - (excluded + (1 - expect law failure) *
        (expect law value - excluded))| ≤ error + 4 * bound * epsilon + 4 * bound * gamma := by
  have centeredBounded : ∀ point, |valueOf point - excluded| ≤ 2 * bound := by
    intro point
    calc |valueOf point - excluded| ≤ |valueOf point| + |excluded| := abs_sub _ _
      _ ≤ 2 * bound := by linarith [valueBounded point, excludedBounded]
  have covariance := abs_expect_mul_sub_le_of_decorrelated law record hidden decorrelated
    failure (fun h => value h - excluded) lumped (fun point => valueOf point - excluded)
    failureBounded lumpedBounded centeredBounded (fun h => by rw [valueEq]) failureNear
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_constant _ _),
    expect_constant] at covariance
  have near : |expect law payoff -
      expect law (fun h => excluded + (1 - failure h) * (value h - excluded))| ≤ error := by
    have upper := expect_mono (μ := law)
      (f := fun h => payoff h - (excluded + (1 - failure h) * (value h - excluded)))
      (g := fun h => |payoff h - (excluded + (1 - failure h) * (value h - excluded))|)
      (fun _ _ => le_abs_self _) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    have lower := expect_mono (μ := law)
      (f := fun h => (excluded + (1 - failure h) * (value h - excluded)) - payoff h)
      (g := fun h => |payoff h - (excluded + (1 - failure h) * (value h - excluded))|)
      (fun h _ => by rw [← neg_sub]; exact neg_le_abs _)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at upper lower
    rw [abs_le]
    constructor <;> linarith
  rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
    expect_constant] at near
  have centerEq :
      |excluded + expect law (fun h => (1 - failure h) * (value h - excluded)) -
        (excluded + (1 - expect law failure) * (expect law value - excluded))| =
      |expect law (fun h => (1 - failure h) * (value h - excluded)) -
        (1 - expect law failure) * (expect law value - excluded)| := by
    congr 1
    ring
  calc
    _ ≤ |expect law payoff -
          (excluded + expect law (fun h => (1 - failure h) * (value h - excluded)))| +
        |excluded + expect law (fun h => (1 - failure h) * (value h - excluded)) -
          (excluded + (1 - expect law failure) * (expect law value - excluded))| :=
      abs_sub_le _ _ _
    _ ≤ _ := by rw [centerEq]; linarith

end GameTheory.Math.Probability
