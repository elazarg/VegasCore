/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Expectation

/-! # Expectations through a gate

A law on points, some of which pass a gate, is compared with a reference law
that dominates its passing readouts pointwise
(`GameTheory.Math.Probability.expect_option_le_of_dominated`). If every point
that fails the gate has value at most a floor, and every reference outcome has a
value at least the floor and above the value of every passing readout, the
expected value of the law is at most the reference's
(`GameTheory.Math.Probability.expect_le_of_gated`).
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {Ω β ρ : Type*}

/-- **Dominated passing readouts.** If a law on optional values puts at most
the reference mass on every present value, a nonnegative bounded payoff of the
present values, zero when absent, has at most the reference expectation. -/
theorem expect_option_le_of_dominated {A : PMF (Option β)} {B : PMF β}
    (dominated : ∀ value, A (some value) ≤ B value) {f : β → ℝ} (nonneg : ∀ value, 0 ≤ f value)
    {C : ℝ} (bounded : ∀ value, f value ≤ C) :
    expect A (fun outcome => outcome.elim 0 f) ≤ expect B f := by
  unfold expect
  have absent : ∀ outcome ∉ Set.range (some : β → Option β),
      (A outcome).toReal * outcome.elim 0 f = 0 := by
    intro outcome outside
    cases outcome with
    | none => simp
    | some value => exact (outside ⟨value, rfl⟩).elim
  rw [← (Option.some_injective β).tsum_eq (f := fun outcome =>
    (A outcome).toReal * outcome.elim 0 f) (fun outcome member => by
      by_contra outside
      exact member (absent outcome outside))]
  have weights (law : β → ℝ) (summable : Summable law) (nonnegLaw : ∀ value, 0 ≤ law value) :
      Summable fun value => law value * f value :=
    Summable.of_nonneg_of_le (fun value => mul_nonneg (nonnegLaw value) (nonneg value))
      (fun value => mul_le_mul_of_nonneg_left (bounded value) (nonnegLaw value))
      (summable.mul_right C)
  apply Summable.tsum_le_tsum (fun value => ?_)
    (weights _ ((pmf_weight_summable A).comp_injective (Option.some_injective β))
      fun _ => ENNReal.toReal_nonneg)
    (weights _ (pmf_weight_summable B) fun _ => ENNReal.toReal_nonneg)
  exact mul_le_mul_of_nonneg_right
    (ENNReal.toReal_mono (B.apply_ne_top value) (dominated value)) (nonneg value)

open Classical in
/-- **A gated law against a dominating reference.** Let the readouts of the
points that pass a gate have at most the reference mass at every present
outcome. If every supported point failing the gate has value at most a floor, and every
reference outcome has a value at least the floor and at least the value of the
present readout, the law's expected value is at most the reference's. -/
theorem expect_le_of_gated (law : PMF Ω) (passes : Ω → Prop) (read : Ω → Option β)
    (reference : PMF β)
    (dominated : ∀ outcome, (law.map fun point => if passes point then some (read point)
      else none) (some outcome) ≤ (reference.map some) outcome)
    (value : Option β → ℝ) (better : β → ℝ) (floor : ℝ) {C : ℝ}
    (valueBounded : ∀ outcome, |value outcome| ≤ C)
    (betterBounded : ∀ outcome, |better outcome| ≤ C)
    (failing : ∀ point ∈ law.support, ¬ passes point → value (read point) ≤ floor)
    (above : ∀ outcome, value (some outcome) ≤ better outcome)
    (atLeast : ∀ outcome, floor ≤ better outcome) :
    expect law (fun point => value (read point)) ≤ expect reference better := by
  -- The excess over the floor of a present readout.
  let excess : Option β → ℝ := fun outcome =>
    outcome.elim (max (value none - floor) 0) fun result => better result - floor
  have excessNonneg (outcome : Option β) : 0 ≤ excess outcome := by
    cases outcome with
    | none => exact le_max_right _ _
    | some result => exact sub_nonneg.mpr (atLeast result)
  have constantNonneg : 0 ≤ C := (abs_nonneg _).trans (valueBounded none)
  have excessBounded (outcome : Option β) : excess outcome ≤ C + |floor| := by
    have floorLe := neg_abs_le floor
    cases outcome with
    | none =>
        refine max_le ?_ (by linarith [abs_nonneg floor])
        linarith [le_abs_self (value none), valueBounded none]
    | some result =>
        change better result - floor ≤ _
        linarith [le_abs_self (better result), betterBounded result]
  let gate := fun point : Ω => if passes point then some (read point) else none
  let gated := fun point : Ω => (gate point).elim 0 excess
  have below (point : Ω) (supported : point ∈ law.support) :
      value (read point) ≤ floor + gated point := by
    by_cases passing : passes point
    · simp only [gated, gate, passing, ↓reduceIte, Option.elim_some]
      cases reading : read point with
      | none =>
          simp only [excess, Option.elim_none]
          linarith [le_max_left (value none - floor) 0]
      | some result =>
          simp only [excess, Option.elim_some]
          linarith [above result]
    · simp only [gated, gate, passing, ↓reduceIte, Option.elim_none]
      linarith [failing point supported passing]
  have gatedBounded (point : Ω) : |gated point| ≤ C + |floor| := by
    have nonneg : 0 ≤ gated point := by
      simp only [gated]
      cases gate point with
      | none => exact le_rfl
      | some outcome => exact excessNonneg outcome
    rw [abs_of_nonneg nonneg]
    simp only [gated]
    cases gate point with
    | none =>
        simp only [Option.elim_none]
        linarith [abs_nonneg floor]
    | some outcome => exact excessBounded outcome
  have integrableValue : PayoffIntegrable law fun point => value (read point) :=
    payoffIntegrable_of_bounded law _ (C := C) fun point => valueBounded _
  have integrableGated : PayoffIntegrable law gated :=
    payoffIntegrable_of_bounded law _ gatedBounded
  have integrableConstant := payoffIntegrable_constant law floor
  calc expect law (fun point => value (read point))
      ≤ expect law (fun point => floor + gated point) :=
        expect_mono (fun point supported => below point supported) integrableValue
          (payoffIntegrable_add integrableConstant integrableGated)
    _ = floor + expect (law.map gate) (fun outcome => outcome.elim 0 excess) := by
        rw [expect_add integrableConstant integrableGated, expect_constant, expect_map]
        rfl
    _ ≤ floor + expect (reference.map some) excess := by
        exact add_le_add le_rfl
          (expect_option_le_of_dominated dominated excessNonneg excessBounded)
    _ = floor + expect reference (fun outcome => better outcome - floor) := by
        rw [expect_map]
        rfl
    _ = expect reference better := by
        have integrableBetter : PayoffIntegrable reference better :=
          payoffIntegrable_of_bounded reference _ betterBounded
        rw [expect_sub integrableBetter (payoffIntegrable_constant reference floor),
          expect_constant]
        ring

end GameTheory.Math.Probability
