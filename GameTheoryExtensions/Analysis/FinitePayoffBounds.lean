/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.EnforcementSynthesis

/-! # Fixed payoff bounds from a finite carrier

Ordered payoffs on a finite nonempty carrier determine extrema. Rational
payoffs give executable bounds and sanction inference.
Every distribution on that carrier satisfies the resulting bounds, so the
range bounds all continuation gains without enumerating strategy profiles.
The existing sanction checker then computes the range divided by a positive
additional collection rate. This is sufficient for the range certificate;
it need not be the least deposit for the particular game's actual comparisons.

Instantiating the carrier with all legal protocol histories includes every
continuation and fixes the bounds before choosing a strategy or assessment.
-/

namespace GameTheory.FinitePayoffBounds

open Math.Probability

variable {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]

section Ordered

variable {Value : Type*} [LinearOrder Value]

def lower (payoff : Outcome → Value) : Value :=
  (Finset.univ.image payoff).min' (Finset.univ_nonempty.image payoff)

def upper (payoff : Outcome → Value) : Value :=
  (Finset.univ.image payoff).max' (Finset.univ_nonempty.image payoff)

theorem lower_le (payoff : Outcome → Value) (outcome : Outcome) : lower payoff ≤ payoff outcome :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem payoff (Finset.mem_univ outcome))

theorem le_upper (payoff : Outcome → Value) (outcome : Outcome) : payoff outcome ≤ upper payoff :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem payoff (Finset.mem_univ outcome))

theorem lower_le_upper (payoff : Outcome → Value) : lower payoff ≤ upper payoff := by
  obtain ⟨outcome⟩ := ‹Nonempty Outcome›
  exact (lower_le payoff outcome).trans (le_upper payoff outcome)

end Ordered

def range (payoff : Outcome → ℚ) : ℚ := upper payoff - lower payoff

theorem range_nonnegative (payoff : Outcome → ℚ) : 0 ≤ range payoff :=
  sub_nonneg.mpr (lower_le_upper payoff)

/-- This bound includes arbitrary randomized continuation strategies. -/
theorem lower_le_expect (payoff : Outcome → ℚ) (law : PMF Outcome) :
    ((lower payoff : ℚ) : ℝ) ≤ expect law (fun outcome => (payoff outcome : ℝ)) := by
  rw [← expect_constant law ((lower payoff : ℚ) : ℝ)]
  apply FinDist.expect_mono
  intro outcome _
  exact_mod_cast lower_le payoff outcome

theorem expect_le_upper (payoff : Outcome → ℚ) (law : PMF Outcome) :
    expect law (fun outcome => (payoff outcome : ℝ)) ≤ ((upper payoff : ℚ) : ℝ) := by
  rw [← expect_constant law ((upper payoff : ℚ) : ℝ)]
  apply FinDist.expect_mono
  intro outcome _
  exact_mod_cast le_upper payoff outcome

theorem expect_gain_le_range (payoff : Outcome → ℚ)
    (prescribed alternative : PMF Outcome) :
    expect alternative (fun outcome => (payoff outcome : ℝ)) -
      expect prescribed (fun outcome => (payoff outcome : ℝ)) ≤ (range payoff : ℝ) := by
  have bounded := sub_le_sub (expect_le_upper payoff alternative)
    (lower_le_expect payoff prescribed)
  simpa only [range, Rat.cast_sub] using bounded

/-- The existing executable checker returns the usual range/rate deposit.
The rate must bound additional collection, not merely the chance that some
charge was collected earlier in the game. -/
theorem infer_range_deposit (payoff : Outcome → ℚ) (rate : ℚ) (positive : 0 < rate) :
    Enforcement.inferScalarDeposit {()} (fun _ => range payoff) (fun _ => rate) =
      some (range payoff / rate) := by
  have detectable : ∀ index ∈ ({()} : Finset Unit), rate = 0 → range payoff ≤ 0 := by
    intro _ _ zero
    exact (positive.ne' zero).elim
  rw [Enforcement.inferScalarDeposit, ite_eq_left detectable, Enforcement.scalarDeposit]
  simp only [Finset.image_singleton, Finset.max'_pair,
    max_eq_right (div_nonneg (range_nonnegative payoff) positive.le)]

/-- A single range certificate covers every actual pair of laws with the
specified additional collection probability. No strategy enumeration or
equilibrium assumption is needed to justify the gain row. -/
theorem range_deposit_holds (payoff : Outcome → ℚ) (rate : ℚ) (positive : 0 < rate)
    (comparison : IncentiveComparison Outcome) (sanction : Set Outcome)
    (collection : (rate : ℝ) ≤ (comparison.alternative.toOuterMeasure sanction).toReal -
      (comparison.prescribed.toOuterMeasure sanction).toReal) :
    comparison.Holds (Enforcement.sanctionedUtility
      (fun outcome => (payoff outcome : ℝ)) sanction (range payoff / rate : ℚ)) := by
  apply Enforcement.inferred_deposit_holds {()} (fun _ => range payoff) (fun _ => rate)
    (fun _ _ => positive.le) (infer_range_deposit payoff rate positive)
    (fun _ => comparison) (fun outcome => (payoff outcome : ℝ)) sanction
    (fun _ _ => expect_gain_le_range payoff comparison.prescribed comparison.alternative)
    (fun _ _ => collection) (Finset.mem_singleton_self ())

end GameTheory.FinitePayoffBounds
