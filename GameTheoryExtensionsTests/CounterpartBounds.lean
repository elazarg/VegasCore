/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.CounterpartBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Two bad histories with one shared good counterpart

The bad weights are each `1/4`, while their shared good counterpart has weight
`1`. Multiplicity two gives the exact normalized bound `1/3`; pretending that
the counterpart is injective would give the false bound `1/5`.
-/

noncomputable section

namespace GameTheoryExtensionsTests.CounterpartBounds

open GameTheory.Math.Probability Finset

private def weight (history : Fin 3) : ℝ := if history = 2 then 1 else 1 / 4
private def bad (history : Fin 3) : Prop := history ≠ 2
private instance : DecidablePred bad := fun history => inferInstanceAs (Decidable (history ≠ 2))
private def counterpart (_ : Fin 3) : Fin 3 := 2

private theorem weight_nonnegative (history : Fin 3) : 0 ≤ weight history := by
  unfold weight
  split <;> norm_num

private theorem counterpart_good (history : Fin 3) (_ : bad history) :
    ¬ bad (counterpart history) := by simp [bad, counterpart]

private theorem fibers (history : Fin 3) (_ : ¬ bad history) :
    ((univ.filter bad).filter fun original => counterpart original = history).card ≤ 2 := by
  fin_cases history <;> decide

private theorem dominated (history : Fin 3) (isBad : bad history) :
    weight history ≤ (1 / 4 : ℝ) * weight (counterpart history) := by
  simp [weight, counterpart, bad] at isBad ⊢
  simp [isBad]

/-- The generic fiber theorem yields the exact unnormalized bound `1/2`. -/
theorem bad_reach_bound : ∑ history with bad history, weight history ≤ (1 : ℝ) / 2 := by
  have bound := sum_weights_le_of_bounded_counterpart weight bad counterpart 2
    weight_nonnegative (by norm_num : (0 : ℝ) ≤ 1 / 4) counterpart_good fibers dominated
  convert bound using 1; norm_num [sum_filter, Fin.sum_univ_succ, bad, weight]

/-- Normalizing the actual weights attains the generic bound `c / (1 + c)`. -/
theorem bad_normalized_bound :
    (∑ history with bad history, weight history) / (∑ history, weight history) ≤ (1 : ℝ) / 3 := by
  have bound := sum_weights_div_sum_le_of_bounded_counterpart weight bad counterpart 2
    weight_nonnegative (by norm_num [Fin.sum_univ_succ, weight])
    (by norm_num : (0 : ℝ) ≤ 1 / 4) counterpart_good fibers dominated
  convert bound using 1; norm_num

theorem bad_normalized_mass :
    (∑ history with bad history, weight history) / (∑ history, weight history) = (1 : ℝ) / 3 := by
  norm_num [sum_filter, Fin.sum_univ_succ, bad, weight]

/-- Ignoring the two-to-one fiber would produce a false normalized bound. -/
theorem injective_bound_fails :
    ¬ (∑ history with bad history, weight history) / (∑ history, weight history) ≤
      (1 / 4 : ℝ) / (1 + 1 / 4) := by
  rw [bad_normalized_mass]
  norm_num

end GameTheoryExtensionsTests.CounterpartBounds
