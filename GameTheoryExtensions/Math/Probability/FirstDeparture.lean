/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Tremble

/-! # Bounding first departures in finite interaction

A kernel may behave arbitrarily after departure. If a compliant state has
departure probability at most delta in its next step, n steps have departure
probability at most the initial probability plus n times delta. The carrier can
be complete histories, so this bound does not assume a memoryless service.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {State : Type*}

/-- Only behavior before the first departure needs a probability bound. -/
theorem departure_bind_bound (law : FinDist State) (kernel : State → FinDist State)
    (bad : Set State) (delta : ℝ) (nonnegative : 0 ≤ delta)
    (first : ∀ state, state ∉ bad → (kernel state).probOf bad ≤ delta) :
    (law.bind kernel).probOf bad ≤ law.probOf bad + delta := by
  classical
  rw [probOf_bind, ← expect_indicator_eq_probOf law bad, ← expect_const law delta,
    ← expect_add]
  apply expect_mono
  intro state _
  by_cases departed : state ∈ bad
  · simp only [departed, ↓reduceIte]
    have atMostOne : (kernel state).probOf bad ≤ 1 := by
      rw [← expect_indicator_eq_probOf, ← expect_const (kernel state) (1 : ℝ)]
      apply expect_mono
      intro next _
      split_ifs <;> norm_num
    linarith
  · simpa only [departed, ↓reduceIte, zero_add] using first state departed

/-- Uniform one-step bounds control all finite prefixes, independently of
which policies complete histories after a departure. -/
theorem departure_iterate_bound (law : FinDist State) (kernel : State → FinDist State)
    (bad : Set State) (delta : ℝ) (nonnegative : 0 ≤ delta)
    (first : ∀ state, state ∉ bad → (kernel state).probOf bad ≤ delta) (steps : Nat) :
    ((fun distribution => distribution.bind kernel)^[steps] law).probOf bad ≤
      law.probOf bad + steps * delta := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      have bound := departure_bind_bound
        ((fun distribution => distribution.bind kernel)^[steps] law) kernel bad delta
        nonnegative first
      push_cast
      nlinarith

end GameTheory.Math.Probability.FinDist
