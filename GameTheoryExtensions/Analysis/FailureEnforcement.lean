/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist

/-! # Failure as a continuation punishment

A caught deviation is assigned its actual failure-continuation value; an
undetected deviation receives its actual missed-continuation value. This
finite expected-utility calculation applies to actor exclusion or global
abort only after their respective continuation values have been established.
There is no inference from a result being called failure to a utility loss,
no detection or collection implementation, and no extended-real utility.
-/

noncomputable section

namespace GameTheory.Enforcement

open Math.Probability
/-- A detection distribution induces the caught/missed continuation mixture.
`true` means caught. The two rewards can already include subsequent rational
responses, old sanctions and all retained source payoffs. -/
def caughtContinuation (detected : FinDist Bool) (failure missed : ℝ) : FinDist ℝ :=
  detected.map (fun caught => if caught then failure else missed)

theorem caught_continuation_value (detected : FinDist Bool) (failure missed : ℝ) :
    (caughtContinuation detected failure missed).expect id =
      detected.prob true * failure + (1 - detected.prob true) * missed := by
  rw [caughtContinuation, FinDist.expect_map, FinDist.expect_eq_sum, Fintype.sum_bool]
  have total : detected.prob false + detected.prob true = 1 := by
    have total := FinDist.expect_const detected (1 : ℝ)
    simpa [FinDist.expect_eq_sum, Fintype.sum_bool, add_comm] using total
  simp only [Bool.false_eq_true, ↓reduceIte, id_eq]
  rw [show detected.prob false = 1 - detected.prob true by linarith]

/-- A probability-weighted *loss relative to the missed continuation* must
cover the deviation gain. Merely naming the caught result `failure` is empty
without establishing its utility. -/
theorem failure_deterrence_iff (detected : FinDist Bool) (failure missed lawful : ℝ) :
    (caughtContinuation detected failure missed).expect id ≤ lawful ↔
      missed - lawful ≤ detected.prob true * (missed - failure) := by
  rw [caught_continuation_value]
  constructor <;> intro bound <;> nlinarith

/-- If failing is at least as good as lawful continuation, every positive
chance of avoiding detection preserves a strictly profitable deviation. -/
theorem failure_without_loss_insufficient (detected : FinDist Bool)
    (failure missed lawful : ℝ)
    (noLoss : lawful ≤ failure) (gain : lawful < missed)
    (imperfect : detected.prob true < 1) :
    lawful < (caughtContinuation detected failure missed).expect id := by
  rw [caught_continuation_value]
  have nonnegative := detected.prob_nonneg true
  have weightedLoss := mul_nonneg nonnegative (sub_nonneg.mpr noLoss)
  have weightedGain := mul_pos (sub_pos.mpr imperfect) (sub_pos.mpr gain)
  nlinarith

/-- Certain detection rewards the departure if failure avoids a costly
obligation and has greater utility than its lawful continuation. -/
theorem certain_failure_can_reward (failure lawful : ℝ) (avoidsCost : lawful < failure)
    (missed : ℝ) :
    lawful < (caughtContinuation (FinDist.pure true) failure missed).expect id := by
  simpa [caughtContinuation] using avoidsCost

/-- With certain detection, deterrence holds exactly when the failure
continuation is no better than compliance. Nothing about the missed branch
matters, and equality permits additional equilibria by indifference. -/
theorem certain_failure_deterrence_iff (failure missed lawful : ℝ) :
    (caughtContinuation (FinDist.pure true) failure missed).expect id ≤ lawful ↔
      failure ≤ lawful := by
  simp [caughtContinuation]

/-- The detection probability need not be one: any sufficiently bad finite
failure payoff works when there is a positive detection probability. -/
theorem finite_failure_suffices (detected : FinDist Bool) (missed lawful : ℝ)
    (positive : 0 < detected.prob true) :
    ∃ failure : ℝ, (caughtContinuation detected failure missed).expect id ≤ lawful := by
  refine ⟨missed - (missed - lawful) / detected.prob true, ?_⟩
  rw [failure_deterrence_iff]
  have nonzero := ne_of_gt positive
  field_simp
  nlinarith

/-- An already imposed debit cannot make a later failure more costly at the
margin: subtracting it from both continuations preserves their comparison. -/
theorem old_charge_cancels (detected : FinDist Bool) (failure missed lawful oldCharge : ℝ) :
    (caughtContinuation detected (failure - oldCharge) (missed - oldCharge)).expect id ≤
      lawful - oldCharge ↔
    (caughtContinuation detected failure missed).expect id ≤ lawful := by
  rw [caught_continuation_value, caught_continuation_value]
  constructor <;> intro bound <;> nlinarith

end GameTheory.Enforcement
