/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.TotalVariation
import GameTheoryExtensions.Math.Probability.PresentConditional

/-! # Conditioning costs only the excluded mass times the payoff oscillation -/

noncomputable section

namespace GameTheory.Math.Probability

/-- Filtering differs from the original law by at most the excluded probability.
No finiteness or independence assumption is needed. -/
theorem filter_withinTV {α : Type*} (law : PMF α) (event : Set α)
    (present : ∃ value ∈ event, value ∈ law.support) :
    PMF.WithinTV (law.toOuterMeasure eventᶜ).toReal (law.filter event present) law := by
  classical
  let mass := (law.toOuterMeasure event).toReal
  have small : mass ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one law event)
  have dominated (value) : mass * ((law.filter event present) value).toReal ≤
      (law value).toReal := by
    have restricted := congrArg ENNReal.toReal (filter_mass_mul law event present value)
    rw [ENNReal.toReal_mul, ← PMF.toOuterMeasure_apply] at restricted
    change mass * ((law.filter event present) value).toReal = _ at restricted
    rw [restricted]
    by_cases included : value ∈ event
    · rw [Set.indicator_of_mem included]
    · rw [Set.indicator_of_notMem included, ENNReal.toReal_zero]
      exact ENNReal.toReal_nonneg
  have total : (law.toOuterMeasure event).toReal +
      (law.toOuterMeasure eventᶜ).toReal = 1 := by
    rw [← expect_indicator, ← expect_indicator,
      ← expect_add (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split_ifs <;> norm_num)
        (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split_ifs <;> norm_num)]
    calc
      _ = expect law (fun _ => (1 : ℝ)) := by
        apply expect_congr_on_support
        intro value _
        by_cases included : value ∈ event <;> simp [included]
      _ = 1 := expect_constant _ _
  have complement : (law.toOuterMeasure eventᶜ).toReal = 1 - mass := by
    dsimp only [mass]
    linarith
  rw [complement]
  exact PMF.WithinTV.of_domination (law.filter event present) law mass small dominated

/-- Conditioning changes a payoff expectation by at most its supportwise
oscillation times the excluded probability. The bounds supply integrability. -/
theorem abs_expect_filter_sub_le {α : Type*} (law : PMF α) (event : Set α)
    (present : ∃ value ∈ event, value ∈ law.support) (payoff : α → ℝ) (low range : ℝ)
    (bounded : ∀ value ∈ law.support, low ≤ payoff value ∧ payoff value ≤ low + range) :
    |expect (law.filter event present) payoff - expect law payoff| ≤
      range * (law.toOuterMeasure eventᶜ).toReal := by
  have close := filter_withinTV law event present
  have compared := close.abs_expect_sub_le_interval payoff low range (by
    intro value supported
    apply bounded value
    rcases supported with retained | original
    · exact ((PMF.mem_support_filter_iff present).mp retained).2
    · exact original)
  exact compared.trans_eq (mul_comm _ _)

end GameTheory.Math.Probability
