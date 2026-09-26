/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Convergence

/-! # Conditioning after a uniformly small multiplicative loss

Point probabilities inside an information event may all shrink, and the event
itself may become arbitrarily rare. If their multiplicative losses uniformly
vanish, conditioning preserves the same limit. No positive limiting event mass
is assumed. The finite carrier is only used to sum the pointwise comparisons.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

namespace FinDist

variable {α : Type*} [Finite α]

private theorem event_mass_bounds (source target : FinDist α) (event : Set α)
    (factor : ℝ)
    (lower : ∀ value ∈ event, factor * source.prob value ≤ target.prob value)
    (upper : ∀ value ∈ event, target.prob value ≤ source.prob value) :
    factor * source.probOf event ≤ target.probOf event ∧
      target.probOf event ≤ source.probOf event := by
  classical
  let _ := Fintype.ofFinite α
  simp only [← expect_indicator_eq_probOf, expect_eq_sum]
  rw [Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro value _
  · by_cases member : value ∈ event
    · simpa only [ite_eq_left member, mul_one] using lower value member
    · simp only [ite_eq_right member, mul_zero, le_refl]
  · by_cases member : value ∈ event
    · simpa only [ite_eq_left member, mul_one] using upper value member
    · simp only [ite_eq_right member, mul_zero, le_refl]

private theorem ratio_difference_bound (original changed factor : ℝ)
    (originalAtMostOne : original ≤ 1)
    (factorPositive : 0 < factor) (factorAtMostOne : factor ≤ 1)
    (lower : factor * original ≤ changed) (upper : factor * changed ≤ original) :
    |changed - original| ≤ (1 - factor) / factor := by
  have lossNonnegative : 0 ≤ 1 - factor := sub_nonneg.mpr factorAtMostOne
  have originalLoss : (1 - factor) * original ≤ 1 - factor :=
    mul_le_of_le_one_right lossNonnegative originalAtMostOne
  have lossLeRatio : 1 - factor ≤ (1 - factor) / factor := by
    apply (le_div_iff₀ factorPositive).mpr
    exact mul_le_of_le_one_right lossNonnegative factorAtMostOne
  apply abs_le.mpr
  constructor
  · have : original - changed ≤ 1 - factor := by nlinarith
    linarith
  · apply (le_div_iff₀ factorPositive).mpr
    nlinarith

/-- Uniformly shrinking each point in the conditioning event by a factor
between `1 - loss` and `1` changes any posterior coordinate by at most
`loss / (1 - loss)`, independently of how small the event's mass is. -/
theorem conditional_relative_loss_bound (source target : FinDist α) (event : Set α)
    (sourceMeet : ∃ value ∈ event, value ∈ source.support)
    (targetMeet : ∃ value ∈ event, value ∈ target.support)
    (loss : ℝ) (nonnegative : 0 ≤ loss) (small : loss < 1)
    (lower : ∀ value ∈ event, (1 - loss) * source.prob value ≤ target.prob value)
    (upper : ∀ value ∈ event, target.prob value ≤ source.prob value) (value : α) :
    |(target.condOn event targetMeet).prob value -
      (source.condOn event sourceMeet).prob value| ≤ loss / (1 - loss) := by
  classical
  have factorPositive : 0 < 1 - loss := sub_pos.mpr small
  have sourcePositive := probOf_pos sourceMeet
  have targetPositive := probOf_pos targetMeet
  obtain ⟨massLower, massUpper⟩ := event_mass_bounds source target event (1 - loss) lower upper
  rw [prob_condOn, prob_condOn]
  by_cases member : value ∈ event
  · rw [ite_eq_left member, ite_eq_left member]
    have originalAtMostOne : source.prob value / source.probOf event ≤ 1 := by
      have point := (source.condOn event sourceMeet).prob_le_one value
      rwa [prob_condOn, ite_eq_left member] at point
    have lowerRatio : (1 - loss) * (source.prob value / source.probOf event) ≤
        target.prob value / target.probOf event := by
      calc
        _ = ((1 - loss) * source.prob value) / source.probOf event := by ring
        _ ≤ target.prob value / source.probOf event :=
          div_le_div_of_nonneg_right (lower value member) sourcePositive.le
        _ ≤ _ := div_le_div_of_nonneg_left (target.prob_nonneg value)
          targetPositive massUpper
    have upperRatio : (1 - loss) * (target.prob value / target.probOf event) ≤
        source.prob value / source.probOf event := by
      have bound : target.prob value / target.probOf event ≤
          source.prob value / ((1 - loss) * source.probOf event) :=
        (div_le_div_of_nonneg_right (upper value member) targetPositive.le).trans
          (div_le_div_of_nonneg_left (source.prob_nonneg value)
            (mul_pos factorPositive sourcePositive) massLower)
      have scaled := mul_le_mul_of_nonneg_left bound factorPositive.le
      have cancellation : (1 - loss) *
          (source.prob value / ((1 - loss) * source.probOf event)) =
          source.prob value / source.probOf event := by
        field_simp
      rwa [cancellation] at scaled
    simpa only [sub_sub_cancel] using ratio_difference_bound
      (source.prob value / source.probOf event) (target.prob value / target.probOf event)
      (1 - loss) originalAtMostOne factorPositive (by linarith)
      lowerRatio upperRatio
  · rw [ite_eq_right member, ite_eq_right member, sub_self, abs_zero]
    exact div_nonneg nonnegative factorPositive.le

end FinDist

/-- Uniform relative loss preserves conditional pointwise convergence even
when both sequences' event probabilities tend to zero. -/
theorem conditional_relative_loss_converges {α : Type*} [Finite α]
    (source target : ℕ → FinDist α) (event : Set α)
    (sourceMeet : ∀ n, ∃ value ∈ event, value ∈ (source n).support)
    (targetMeet : ∀ n, ∃ value ∈ event, value ∈ (target n).support)
    (loss : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ loss n) (small : ∀ n, loss n < 1)
    (lower : ∀ n value, value ∈ event →
      (1 - loss n) * (source n).prob value ≤ (target n).prob value)
    (upper : ∀ n value, value ∈ event → (target n).prob value ≤ (source n).prob value)
    (vanishes : Tendsto loss atTop (nhds 0)) (limit : FinDist α)
    (converges : FinDistConvergesPointwise
      (fun n => (source n).condOn event (sourceMeet n)) limit) :
    FinDistConvergesPointwise (fun n => (target n).condOn event (targetMeet n)) limit := by
  have errorVanishes : Tendsto (fun n => loss n / (1 - loss n)) atTop (nhds 0) := by
    simpa only [sub_zero, zero_div] using!
      vanishes.div (tendsto_const_nhds.sub vanishes) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  intro value
  apply (converges value).congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ errorVanishes
  intro n
  simpa only [Real.dist_eq, abs_sub_comm] using
    FinDist.conditional_relative_loss_bound (source n) (target n) event
      (sourceMeet n) (targetMeet n) (loss n) (nonnegative n) (small n)
      (lower n) (upper n) value

end GameTheory.Math.Probability
