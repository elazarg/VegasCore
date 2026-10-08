/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Survival through bounded adaptive opportunities

A transition kernel may depend on the complete history represented by its
state. A lower bound on remaining in an event at every such state multiplies
across a bounded run, without independence between opportunities. The premise
is conditional and pointwise; a bound averaged over an initial law cannot
replace it. These probability results do not supply a blockchain inclusion or
collection guarantee.
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {State : Type*}

/-- A conditional event-survival floor bounds one step under every start law.
States outside the event can add mass, so no absorption assumption is needed. -/
theorem eventProbability_bind_ge (law : PMF State) (kernel : State → PMF State)
    (event : Set State) (floor : ℝ)
    (survival : ∀ state ∈ event, floor ≤ ((kernel state).toOuterMeasure event).toReal) :
    floor * (law.toOuterMeasure event).toReal ≤
      ((law.bind kernel).toOuterMeasure event).toReal := by
  classical
  rw [toReal_toOuterMeasure_bind, ← expect_indicator, ← expect_const_mul]
  apply expect_mono _
    (payoffIntegrable_const_mul (c := floor)
      (payoffIntegrable_ite_one_zero law (· ∈ event)))
    (payoffIntegrable_toReal_toOuterMeasure law kernel event)
  intro state _
  by_cases pending : state ∈ event
  · simpa only [pending, ite_true, mul_one] using survival state pending
  · simp only [pending, ite_false, mul_zero]
    exact ENNReal.toReal_nonneg

/-- A conditional survival floor compounds across any bounded number of
opportunities. The kernel may encode adaptive actions and the entire past. -/
theorem eventProbability_iterate_ge_pow (law : PMF State)
    (kernel : State → PMF State) (event : Set State) (floor : ℝ)
    (nonnegative : 0 ≤ floor)
    (survival : ∀ state ∈ event, floor ≤ ((kernel state).toOuterMeasure event).toReal)
    (count : Nat) :
    floor ^ count * (law.toOuterMeasure event).toReal ≤
      (((fun distribution : PMF State => distribution.bind kernel)^[count] law).toOuterMeasure
        event).toReal := by
  induction count with
  | zero => simp
  | succ count induction =>
      rw [Function.iterate_succ_apply', pow_succ]
      calc
        floor ^ count * floor * (law.toOuterMeasure event).toReal =
            floor * (floor ^ count * (law.toOuterMeasure event).toReal) := by ring
        _ ≤ floor * (((fun distribution : PMF State => distribution.bind kernel)^[count]
              law).toOuterMeasure event).toReal :=
          mul_le_mul_of_nonneg_left induction nonnegative
        _ ≤ _ := eventProbability_bind_ge _ kernel event floor survival

/-- Different conditional survival floors can be used at different
opportunities. The transition list need not consist of independent kernels. -/
theorem eventProbability_foldl_ge_prod (law : PMF State)
    (steps : List (ℝ × (State → PMF State))) (event : Set State)
    (nonnegative : ∀ step ∈ steps, 0 ≤ step.1)
    (survival : ∀ step ∈ steps, ∀ state ∈ event,
      step.1 ≤ ((step.2 state).toOuterMeasure event).toReal) :
    (steps.map Prod.fst).prod * (law.toOuterMeasure event).toReal ≤
      ((steps.foldl (fun (distribution : PMF State) step => distribution.bind step.2)
        law).toOuterMeasure event).toReal := by
  induction steps generalizing law with
  | nil => simp
  | cons step rest induction =>
      have restNonnegative : ∀ next ∈ rest, 0 ≤ next.1 :=
        fun next member => nonnegative next (List.mem_cons_of_mem step member)
      have restSurvival : ∀ next ∈ rest, ∀ state ∈ event,
          next.1 ≤ ((next.2 state).toOuterMeasure event).toReal :=
        fun next member => survival next (List.mem_cons_of_mem step member)
      have productNonnegative : 0 ≤ (rest.map Prod.fst).prod :=
        List.prod_nonneg fun value member => by
          obtain ⟨next, supported, rfl⟩ := List.mem_map.mp member
          exact restNonnegative next supported
      simp only [List.map_cons, List.prod_cons, List.foldl_cons]
      calc
        step.1 * (rest.map Prod.fst).prod * (law.toOuterMeasure event).toReal =
            (rest.map Prod.fst).prod * (step.1 * (law.toOuterMeasure event).toReal) := by ring
        _ ≤ (rest.map Prod.fst).prod * ((law.bind step.2).toOuterMeasure event).toReal :=
          mul_le_mul_of_nonneg_left
            (eventProbability_bind_ge law step.2 event step.1
              (survival step (List.mem_cons_self))) productNonnegative
        _ ≤ _ := induction (law.bind step.2) restNonnegative restSurvival

/-- Starting inside the event, a strictly positive conditional floor gives a
strictly positive chance of remaining there after every finite run. -/
theorem eventProbability_iterate_pos (law : PMF State)
    (kernel : State → PMF State) (event : Set State) (floor : ℝ)
    (positive : 0 < floor) (initial : 0 < (law.toOuterMeasure event).toReal)
    (survival : ∀ state ∈ event, floor ≤ ((kernel state).toOuterMeasure event).toReal)
    (count : Nat) :
    0 < (((fun distribution : PMF State => distribution.bind kernel)^[count] law).toOuterMeasure
      event).toReal :=
  (mul_pos (pow_pos positive count) initial).trans_le
    (eventProbability_iterate_ge_pow law kernel event floor positive.le survival count)

end GameTheory.Math.Probability
