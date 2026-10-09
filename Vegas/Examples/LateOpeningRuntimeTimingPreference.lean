/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Impossibility

/-! # Three-label timing preferences with a nonzero failure contribution

These algebraic adapters concern specified continuation values. They do not
assert that a runtime realizes those values. The native payoff proofs supply
that separate identification. Positive reward and any positive failure
probability make the failure contribution nonzero for at least one original
bit, whatever the receiver guesses without observing the opening.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeTimingPreference

/-- The existing three-label sign argument applies to numerical private labels. -/
theorem opposite_label_preferences (difference : Fin 3 → ℝ) (pull leak : ℝ)
    (zero : difference 0 = pull + leak) (one : difference 1 = pull - leak)
    (two : difference 2 = -pull) (separates : leak ≠ 0) :
    ∃ sender holder, 0 < difference sender ∧ difference holder < 0 := by
  obtain ⟨sender, holder, positive, negative⟩ :=
    lateLeak_opposite_label_preferences pull leak separates
  let number : LateLeakLabel → Fin 3
    | .a => 0
    | .b => 1
    | .c => 2
  have same (label : LateLeakLabel) :
      difference (number label) = lateLeakLabelPreference pull leak label := by
    cases label
    · exact zero
    · exact one
    · exact two
  exact ⟨number sender, number holder, (same sender).symm ▸ positive,
    (same holder).symm ▸ negative⟩

def failurePull (failure reward emptyTrue : ℝ) (bit : Bool) : ℝ :=
  if bit then failure * reward / 4 * (1 - emptyTrue)
    else -(failure * reward / 4) * emptyTrue

/-- No unseen bit-guess lottery can remove the failure contribution for both bits. -/
theorem failurePull_nonzero (failure reward emptyTrue : ℝ)
    (failurePositive : 0 < failure) (rewardPositive : 0 < reward) :
    ∃ bit, failurePull failure reward emptyTrue bit ≠ 0 := by
  have coefficient : failure * reward / 4 ≠ 0 := (by positivity :
    0 < failure * reward / 4).ne'
  by_cases sure : emptyTrue = 1
  · refine ⟨false, ?_⟩
    simpa only [failurePull, Bool.false_eq_true, ↓reduceIte, sure, mul_one] using
      neg_ne_zero.mpr coefficient
  · refine ⟨true, ?_⟩
    simpa only [failurePull, ↓reduceIte] using
      mul_ne_zero coefficient (sub_ne_zero.mpr (Ne.symm sure))

/-- A three-label timing difference with the checked failure contribution has
strict preferences in opposite directions within one original-bit class. -/
theorem opposite_timing_preferences (first second : Bool → Fin 3 → ℝ)
    (pull : Bool → ℝ) (failure reward emptyTrue : ℝ)
    (failurePositive : 0 < failure) (rewardPositive : 0 < reward)
    (zero : ∀ bit, first bit 0 - second bit 0 =
      pull bit + failurePull failure reward emptyTrue bit)
    (one : ∀ bit, first bit 1 - second bit 1 =
      pull bit - failurePull failure reward emptyTrue bit)
    (two : ∀ bit, first bit 2 - second bit 2 = -pull bit) :
    ∃ bit sender holder, second bit sender < first bit sender ∧
      first bit holder < second bit holder := by
  obtain ⟨bit, separates⟩ := failurePull_nonzero failure reward emptyTrue
    failurePositive rewardPositive
  obtain ⟨sender, holder, positive, negative⟩ := opposite_label_preferences
    (fun label => first bit label - second bit label) (pull bit)
      (failurePull failure reward emptyTrue bit) (zero bit) (one bit) (two bit) separates
  exact ⟨bit, sender, holder, sub_pos.mp positive, sub_neg.mp negative⟩

/-- With at least one successful transcript never selecting Safe, either of
the two low-numbered labels has a three-quarter-reward success floor. -/
theorem successful_first_floor (reward seenSafe unseenSafe : ℝ)
    (rewardNonnegative : 0 ≤ reward) (seenSafeBelow : seenSafe ≤ 1)
    (unseenSafeBelow : unseenSafe ≤ 1) (oneZero : seenSafe = 0 ∨ unseenSafe = 0) :
    3 * reward / 4 ≤
      (reward * (1 - seenSafe / 2) + reward * (1 - unseenSafe / 2)) / 2 := by
  rcases oneZero with zero | zero
  · rw [zero]
    nlinarith [mul_nonneg rewardNonnegative (sub_nonneg.mpr unseenSafeBelow)]
  · rw [zero]
    nlinarith [mul_nonneg rewardNonnegative (sub_nonneg.mpr seenSafeBelow)]

/-- A finite positive outage small enough for this inequality makes that
first-opening floor strictly exceed the source Safe payoff. -/
theorem first_floor_exceeds_safe (reward failure loss : ℝ)
    (rewardPositive : 0 < reward) (lossNonnegative : 0 ≤ loss)
    (failureSmall : failure < reward / (3 * reward + 4 * loss)) :
    reward / 2 < 3 * (1 - failure) * reward / 4 - failure * loss := by
  have denominator : 0 < 3 * reward + 4 * loss := by positivity
  have small := (lt_div_iff₀ denominator).mp failureSmall
  nlinarith

end Vegas.Examples.LateOpeningRuntimeTimingPreference
