/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.OptionalDomination

/-! # Expectations through a gate

A law on points, some of which pass a gate, is compared with a reference law
that dominates its passing readouts pointwise. If every point
that fails the gate has value at most a floor, and every reference outcome has a
value at least the floor and above the value of every passing readout, the
expected value of the law is at most the reference's
(`GameTheory.Math.Probability.expect_le_of_gated`).
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {Ω β ρ : Type*}

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
  let lifted : Option β → ℝ := fun outcome => outcome.elim (value none) better
  have valueIntegrable : PayoffIntegrable law (fun point => value (read point)) :=
    payoffIntegrable_of_bounded law _ fun point => valueBounded (read point)
  have betterIntegrable : PayoffIntegrable (reference.map some) lifted := by
    rw [payoffIntegrable_map_iff]
    exact payoffIntegrable_of_bounded reference _ betterBounded
  have bound := expect_le_of_dominated_readout law (reference.map some)
    (fun point => if passes point then some (read point) else none) dominated
    (fun point => value (read point)) lifted valueIntegrable betterIntegrable (by
      intro point _ outcome reading
      by_cases passing : passes point
      · simp only [passing, ↓reduceIte, Option.some.injEq] at reading
        subst outcome
        cases read point with
        | none => exact le_rfl
        | some result => exact above result
      · simp [passing] at reading) (by
      intro point supported reading outcome member
      have notPassing : ¬ passes point := by
        intro passing
        simp [passing] at reading
      obtain ⟨result, _, rfl⟩ := PMF.support_map .. ▸ member
      exact (failing point supported notPassing).trans (atLeast result))
  simpa only [expect_map, Function.comp_def, lifted, Option.elim_some] using bound

end GameTheory.Math.Probability
