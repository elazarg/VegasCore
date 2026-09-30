/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Expectation

/-! # Bounding first departures in finite interaction

A kernel may behave arbitrarily after departure. If a compliant state has
departure probability at most delta in its next step, n steps have departure
probability at most the initial probability plus n times delta. The carrier can
be complete histories, so this bound does not assume a memoryless service.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {State : Type*}

/-- Only behavior before the first departure needs a probability bound. -/
theorem departure_bind_bound (law : PMF State) (kernel : State → PMF State)
    (bad : Set State) (delta : ℝ) (nonnegative : 0 ≤ delta)
    (first : ∀ state, state ∉ bad → ((kernel state).toOuterMeasure bad).toReal ≤ delta) :
    ((law.bind kernel).toOuterMeasure bad).toReal ≤ (law.toOuterMeasure bad).toReal + delta := by
  classical
  have indicatorIntegrable : PayoffIntegrable law fun state => if state ∈ bad then (1 : ℝ) else 0 :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun state => by split_ifs <;> norm_num
  rw [toReal_toOuterMeasure_bind, ← expect_indicator law bad, ← expect_constant law delta,
    ← expect_add indicatorIntegrable (payoffIntegrable_constant _ _)]
  refine expect_mono (fun state _ => ?_)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun state => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one _ _))
    (payoffIntegrable_add indicatorIntegrable (payoffIntegrable_constant _ _))
  by_cases departed : state ∈ bad
  · simp only [departed, ↓reduceIte]
    have atMostOne : ((kernel state).toOuterMeasure bad).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one _ _)
    linarith
  · simpa only [departed, ↓reduceIte, zero_add] using first state departed

/-- Uniform one-step bounds control all finite prefixes, independently of
which policies complete histories after a departure. -/
theorem departure_iterate_bound (law : PMF State) (kernel : State → PMF State)
    (bad : Set State) (delta : ℝ) (nonnegative : 0 ≤ delta)
    (first : ∀ state,
        state ∉ bad → ((kernel state).toOuterMeasure bad).toReal ≤ delta) (steps : Nat) :
    (((fun distribution => distribution.bind kernel)^[steps] law).toOuterMeasure bad).toReal ≤
      (law.toOuterMeasure bad).toReal + steps * delta := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      have bound := departure_bind_bound
        ((fun distribution => distribution.bind kernel)^[steps] law) kernel bad delta
        nonnegative first
      push_cast
      nlinarith

end PMF
