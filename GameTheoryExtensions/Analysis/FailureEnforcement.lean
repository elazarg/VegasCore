/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

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
def caughtContinuation (detected : PMF Bool) (failure missed : ℝ) : PMF ℝ :=
  detected.map (fun caught => if caught then failure else missed)

theorem caught_continuation_value (detected : PMF Bool) (failure missed : ℝ) :
    expect (caughtContinuation detected failure missed) id =
      (detected true).toReal * failure + (1 - (detected true).toReal) * missed := by
  rw [caughtContinuation, expect_map, expect_eq_sum, Fintype.sum_bool]
  have total := pmf_sum_toReal_eq_one detected
  rw [Fintype.sum_bool] at total
  simp only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte, id_eq]
  rw [show (detected false).toReal = 1 - (detected true).toReal by linarith]

/-- A probability-weighted *loss relative to the missed continuation* must
cover the deviation gain. Merely naming the caught result `failure` is empty
without establishing its utility. -/
theorem failure_deterrence_iff (detected : PMF Bool) (failure missed lawful : ℝ) :
    expect (caughtContinuation detected failure missed) id ≤ lawful ↔
      missed - lawful ≤ (detected true).toReal * (missed - failure) := by
  rw [caught_continuation_value]
  constructor <;> intro bound <;> nlinarith

/-- If failing is at least as good as lawful continuation, every positive
chance of avoiding detection preserves a strictly profitable deviation. -/
theorem failure_without_loss_insufficient (detected : PMF Bool)
    (failure missed lawful : ℝ)
    (noLoss : lawful ≤ failure) (gain : lawful < missed)
    (imperfect : (detected true).toReal < 1) :
    lawful < expect (caughtContinuation detected failure missed) id := by
  rw [caught_continuation_value]
  have nonnegative : 0 ≤ (detected true).toReal := ENNReal.toReal_nonneg
  have weightedLoss := mul_nonneg nonnegative (sub_nonneg.mpr noLoss)
  have weightedGain := mul_pos (sub_pos.mpr imperfect) (sub_pos.mpr gain)
  nlinarith

/-- Certain detection rewards the departure if failure avoids a costly
obligation and has greater utility than its lawful continuation. -/
theorem certain_failure_can_reward (failure lawful : ℝ) (avoidsCost : lawful < failure)
    (missed : ℝ) :
    lawful < expect (caughtContinuation (PMF.pure true) failure missed) id := by
  simpa [caughtContinuation, PMF.pure_map, expect_pure] using avoidsCost

/-- With certain detection, deterrence holds exactly when the failure
continuation is no better than compliance. Nothing about the missed branch
matters, and equality permits additional equilibria by indifference. -/
theorem certain_failure_deterrence_iff (failure missed lawful : ℝ) :
    expect (caughtContinuation (PMF.pure true) failure missed) id ≤ lawful ↔
      failure ≤ lawful := by
  simp [caughtContinuation, PMF.pure_map, expect_pure]

/-- The detection probability need not be one: any sufficiently bad finite
failure payoff works when there is a positive detection probability. -/
theorem finite_failure_suffices (detected : PMF Bool) (missed lawful : ℝ)
    (positive : 0 < (detected true).toReal) :
    ∃ failure : ℝ, expect (caughtContinuation detected failure missed) id ≤ lawful := by
  refine ⟨missed - (missed - lawful) / (detected true).toReal, ?_⟩
  rw [failure_deterrence_iff]
  have nonzero := ne_of_gt positive
  field_simp
  nlinarith

/-- An already imposed debit cannot make a later failure more costly at the
margin: subtracting it from both continuations preserves their comparison. -/
theorem old_charge_cancels (detected : PMF Bool) (failure missed lawful oldCharge : ℝ) :
    expect (caughtContinuation detected (failure - oldCharge) (missed - oldCharge)) id ≤
      lawful - oldCharge ↔
    expect (caughtContinuation detected failure missed) id ≤ lawful := by
  rw [caught_continuation_value, caught_continuation_value]
  constructor <;> intro bound <;> nlinarith

end GameTheory.Enforcement
