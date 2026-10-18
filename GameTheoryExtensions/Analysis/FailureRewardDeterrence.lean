/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Expectation

/-! # Aggregate exclusion deterrence for failure rewards

The law is the actual terminal law. Each player has a nonnegative expected
payoff, as supplied by an attainable security policy and Nash optimality.
Survivors can earn only bounded rewards for other players' exclusions. Fixed
exclusion losses above the aggregate reward bound force exclusion-free support.
Nonnegative charges may already have been subtracted from the stated payoffs.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators
open Math.Probability

namespace FailureReward

open Classical in
private theorem normalized_payoff_sum_bound {Player : Type*} [Fintype Player]
    (excluded : Player → Prop) (payoff reward loss : Player → ℝ)
    (positive : ∀ owner, 0 < reward owner)
    (deterrence : ∀ owner,
      ((Fintype.card Player : ℝ) - 1) * reward owner < loss owner)
    (excludedBound : ∀ owner, excluded owner → payoff owner ≤ -loss owner)
    (survivorBound : ∀ owner, ¬excluded owner →
      payoff owner ≤ reward owner *
        ∑ other ∈ Finset.univ.erase owner, if excluded other then (1 : ℝ) else 0) :
    (∑ owner, payoff owner / reward owner) ≤ 0 ∧
      ((∃ owner, excluded owner) → (∑ owner, payoff owner / reward owner) < 0) := by
  let mark : Player → ℝ := fun owner => if excluded owner then 1 else 0
  let total : ℝ := ∑ owner, mark owner
  let benchmark : Player → ℝ := fun owner =>
    total - mark owner - ((Fintype.card Player : ℝ) - 1) * mark owner
  have erased (owner : Player) :
      (∑ other ∈ Finset.univ.erase owner, mark other) = total - mark owner := by
    have partition := Finset.sum_erase_add Finset.univ mark (Finset.mem_univ owner)
    dsimp only [total]
    linarith
  have foreignNonnegative (owner : Player) : 0 ≤ total - mark owner := by
    rw [← erased owner]
    exact Finset.sum_nonneg fun other _ => by simp only [mark]; split <;> norm_num
  have strict (owner : Player) (failed : excluded owner) :
      payoff owner / reward owner < benchmark owner := by
    have lost := excludedBound owner failed
    have margin := deterrence owner
    have divided : payoff owner / reward owner < -((Fintype.card Player : ℝ) - 1) := by
      apply (div_lt_iff₀ (positive owner)).mpr
      nlinarith
    have foreign := foreignNonnegative owner
    dsimp only [benchmark]
    simp only [mark, failed, ite_true, mul_one] at *
    linarith
  have component (owner : Player) : payoff owner / reward owner ≤ benchmark owner := by
    by_cases failed : excluded owner
    · exact (strict owner failed).le
    · have bounded : payoff owner / reward owner ≤
          ∑ other ∈ Finset.univ.erase owner, mark other := by
        apply (div_le_iff₀ (positive owner)).mpr
        simpa only [mark, mul_comm] using survivorBound owner failed
      rw [erased owner] at bounded
      simpa only [benchmark, mark, failed, ite_false, sub_zero, mul_zero] using bounded
  have balanced : (∑ owner, benchmark owner) = 0 := by
    simp only [benchmark, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum]
    change (Fintype.card Player : ℝ) * total - total -
      ((Fintype.card Player : ℝ) - 1) * total = 0
    ring
  constructor
  · exact (Finset.sum_le_sum fun owner _ => component owner).trans_eq balanced
  · rintro ⟨owner, failed⟩
    have smaller := Finset.sum_lt_sum (fun other _ => component other)
      ⟨owner, Finset.mem_univ owner, strict owner failed⟩
    exact smaller.trans_eq balanced

open Classical in
/-- Actual nonnegative expected payoffs and terminal failure-reward bounds
exclude every player from the exclusion set throughout the terminal support.
The security comparison concerns the same terminal law as the payoff bounds. -/
theorem supported_exclusion_free {Player Outcome : Type*}
    [Fintype Player] [Finite Outcome]
    (law : PMF Outcome) (excluded : Player → Outcome → Prop)
    (payoff : Player → Outcome → ℝ) (reward loss : Player → ℝ)
    (positive : ∀ owner, 0 < reward owner)
    (deterrence : ∀ owner,
      ((Fintype.card Player : ℝ) - 1) * reward owner < loss owner)
    (excludedBound : ∀ outcome ∈ law.support, ∀ owner,
      excluded owner outcome → payoff owner outcome ≤ -loss owner)
    (survivorBound : ∀ outcome ∈ law.support, ∀ owner, ¬excluded owner outcome →
      payoff owner outcome ≤ reward owner *
        ∑ other ∈ Finset.univ.erase owner, if excluded other outcome then (1 : ℝ) else 0)
    (security : ∀ owner, 0 ≤ expect law (payoff owner)) :
    ∀ outcome ∈ law.support, ∀ owner, ¬excluded owner outcome := by
  let total : Outcome → ℝ := fun outcome =>
    ∑ owner, payoff owner outcome / reward owner
  have pointwise (outcome : Outcome) (supported : outcome ∈ law.support) :=
    normalized_payoff_sum_bound (fun owner => excluded owner outcome)
      (fun owner => payoff owner outcome) reward loss positive deterrence
      (excludedBound outcome supported) (survivorBound outcome supported)
  have mean : expect law total = ∑ owner, expect law (payoff owner) / reward owner := by
    rw [expect_sum law (fun owner outcome => payoff owner outcome / reward owner)
      (fun _ => payoffIntegrable_of_finite _ _)]
    exact Finset.sum_congr rfl fun owner _ => by
      simp only [div_eq_mul_inv, expect_mul_const]
  have nonnegative : 0 ≤ expect law total := by
    rw [mean]
    exact Finset.sum_nonneg fun owner _ => div_nonneg (security owner) (positive owner).le
  have nonpositive : expect law total ≤ 0 :=
    expect_le_const law total (payoffIntegrable_of_finite _ _) 0
      (fun outcome supported => (pointwise outcome supported).1)
  have zero := expect_eq_const_of_le_on_support law total 0
    (payoffIntegrable_of_finite _ _) (fun outcome supported => (pointwise outcome supported).1)
    (le_antisymm nonpositive nonnegative)
  intro outcome supported owner failed
  have negative := (pointwise outcome supported).2 ⟨owner, failed⟩
  change total outcome < 0 at negative
  rw [zero outcome supported] at negative
  exact (lt_irrefl 0) negative

open Classical in
/-- Every individual exclusion event has probability zero, and the joint
exclusion-free event has probability one under the actual finite law. -/
theorem exclusion_probabilities {Player Outcome : Type*}
    [Fintype Player] [Finite Outcome]
    (law : PMF Outcome) (excluded : Player → Outcome → Prop)
    (payoff : Player → Outcome → ℝ) (reward loss : Player → ℝ)
    (positive : ∀ owner, 0 < reward owner)
    (deterrence : ∀ owner,
      ((Fintype.card Player : ℝ) - 1) * reward owner < loss owner)
    (excludedBound : ∀ outcome ∈ law.support, ∀ owner,
      excluded owner outcome → payoff owner outcome ≤ -loss owner)
    (survivorBound : ∀ outcome ∈ law.support, ∀ owner, ¬excluded owner outcome →
      payoff owner outcome ≤ reward owner *
        ∑ other ∈ Finset.univ.erase owner, if excluded other outcome then (1 : ℝ) else 0)
    (security : ∀ owner, 0 ≤ expect law (payoff owner)) :
    (∀ owner, law.toOuterMeasure {outcome | excluded owner outcome} = 0) ∧
      law.toOuterMeasure {outcome | ∀ owner, ¬excluded owner outcome} = 1 := by
  have safe := supported_exclusion_free law excluded payoff reward loss positive deterrence
    excludedBound survivorBound security
  constructor
  · intro owner
    apply (law.toOuterMeasure_apply_eq_zero_iff _).mpr
    exact Set.disjoint_left.mpr fun outcome supported failed => safe outcome supported owner failed
  · exact (law.toOuterMeasure_apply_eq_one_iff _).mpr fun outcome supported =>
      safe outcome supported

end FailureReward

end GameTheory
