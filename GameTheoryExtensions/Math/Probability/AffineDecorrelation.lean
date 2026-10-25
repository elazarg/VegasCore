/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.ProductDecorrelation

/-! # Affine payoff scores under approximate record independence -/

noncomputable section
namespace GameTheory.Math.Probability

/-- Centering at an exclusion payoff turns a concrete failure/value factor into
an affine scalar score after averaging the actual posterior. The payoff needs
an integration guard; the outcome carrier may be infinite. -/
theorem abs_expect_affine_sub_le_of_decorrelated
    {H R T : Type*} (law : PMF H) (record : H → R) (hidden : H → T)
    {gamma : ℝ} (decorrelated : BeliefDecorrelated law record hidden gamma)
    (failure payoff value : H → ℝ) (lumped : R → ℝ) (valueOf : T → ℝ)
    (excluded : ℝ) {bound error epsilon : ℝ}
    (failureBounded : ∀ h, |failure h| ≤ 1)
    (lumpedBounded : ∀ record, |lumped record| ≤ 1)
    (valueBounded : ∀ point, |valueOf point| ≤ bound)
    (valueEq : ∀ h, value h = valueOf (hidden h))
    (excludedBounded : |excluded| ≤ bound)
    (payoffIntegrable : PayoffIntegrable law payoff)
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
  have valueIntegrable : PayoffIntegrable law value :=
    payoffIntegrable_of_bounded law _ (fun h => by rw [valueEq]; exact valueBounded _)
  rw [expect_sub valueIntegrable (payoffIntegrable_constant _ _), expect_constant] at covariance
  have productIntegrable : PayoffIntegrable law
      (fun h => (1 - failure h) * (value h - excluded)) :=
    payoffIntegrable_of_bounded law _ fun h => by
      rw [abs_mul]
      exact mul_le_mul
        (show |1 - failure h| ≤ 2 by
          rcases abs_le.mp (failureBounded h) with ⟨lower, upper⟩
          rw [abs_le]; constructor <;> linarith)
        (by rw [valueEq]; exact centeredBounded _) (abs_nonneg _) (by norm_num)
  have near := (abs_expect_sub_le_expect_abs_sub law payoff
    (fun h => excluded + (1 - failure h) * (value h - excluded)) payoffIntegrable
    (payoffIntegrable_add (payoffIntegrable_constant _ _) productIntegrable)).trans payoffNear
  rw [expect_add (payoffIntegrable_constant _ _) productIntegrable, expect_constant] at near
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
