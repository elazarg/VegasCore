/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist

/-! # The payoff component affected by correlation

Two laws with the same marginals agree on all additive payoffs. Conversely,
only additive payoffs agree on every such pair of laws; two-by-two balanced
switches suffice to test this. For an arbitrary payoff, its centered interaction
component accounts for the entire expectation difference. No equilibrium or
runtime correspondence is assumed or concluded.
-/

noncomputable section

namespace GameTheory.CorrelationPayoff

open Math.Probability

variable {First Second : Type*}

/-- Remove the two marginal effects using fixed reference distributions. -/
def interaction (left : FinDist First) (right : FinDist Second)
    (payoff : First × Second → ℝ) (outcome : First × Second) : ℝ :=
  payoff outcome - right.expect (fun second => payoff (outcome.1, second)) -
    left.expect (fun first => payoff (first, outcome.2)) +
    left.expect (fun first => right.expect (fun second => payoff (first, second)))

theorem expect_additive_eq (first second : FinDist (First × Second))
    (left : first.map Prod.fst = second.map Prod.fst)
    (right : first.map Prod.snd = second.map Prod.snd)
    (row : First → ℝ) (column : Second → ℝ) :
    first.expect (fun outcome => row outcome.1 + column outcome.2) =
      second.expect (fun outcome => row outcome.1 + column outcome.2) := by
  have rowEq := congrArg (fun law : FinDist First => law.expect row) left
  have columnEq := congrArg (fun law : FinDist Second => law.expect column) right
  simp only [FinDist.expect_map] at rowEq columnEq
  simp only [FinDist.expect_add, rowEq, columnEq]

/-- For unchanged marginals, only the interaction component contributes to
the expectation difference. The reference laws may be chosen independently. -/
theorem expectation_difference_eq_interaction
    (first second : FinDist (First × Second))
    (left : first.map Prod.fst = second.map Prod.fst)
    (right : first.map Prod.snd = second.map Prod.snd)
    (referenceLeft : FinDist First) (referenceRight : FinDist Second)
    (payoff : First × Second → ℝ) :
    first.expect payoff - second.expect payoff =
      first.expect (interaction referenceLeft referenceRight payoff) -
        second.expect (interaction referenceLeft referenceRight payoff) := by
  have rowEq := congrArg (fun law : FinDist First => law.expect
    (fun row => referenceRight.expect (fun col => payoff (row, col)))) left
  have columnEq := congrArg (fun law : FinDist Second => law.expect
    (fun col => referenceLeft.expect (fun row => payoff (row, col)))) right
  simp only [FinDist.expect_map] at rowEq columnEq
  unfold interaction
  simp only [FinDist.expect_add, FinDist.expect_sub, FinDist.expect_const]
  rw [rowEq, columnEq]
  ring

/-- A centered interaction has zero mean on each coordinate of the product
reference distribution. This gives the ordinary two-factor payoff decomposition. -/
theorem interaction_right_mean (left : FinDist First) (right : FinDist Second)
    (payoff : First × Second → ℝ) (row : First) :
    right.expect (fun col => interaction left right payoff (row, col)) = 0 := by
  simp only [interaction, FinDist.expect_add, FinDist.expect_sub, FinDist.expect_const]
  rw [FinDist.expect_comm right left]
  ring

theorem interaction_left_mean (left : FinDist First) (right : FinDist Second)
    (payoff : First × Second → ℝ) (col : Second) :
    left.expect (fun row => interaction left right payoff (row, col)) = 0 := by
  simp only [interaction, FinDist.expect_add, FinDist.expect_sub, FinDist.expect_const]
  ring

/-- The gain or loss from the actual coupling, relative to the product
distribution with exactly the same marginals, is the mean interaction payoff. -/
theorem correlation_gain_eq_interaction (law : FinDist (First × Second))
    (payoff : First × Second → ℝ) :
    law.expect payoff -
        (FinDist.product (law.map Prod.fst) (law.map Prod.snd)).expect payoff =
      law.expect (interaction (law.map Prod.fst) (law.map Prod.snd) payoff) := by
  rw [expectation_difference_eq_interaction law _
    (FinDist.map_fst_product _ _).symm (FinDist.map_snd_product _ _).symm
    (law.map Prod.fst) (law.map Prod.snd), FinDist.expect_product]
  simp only [interaction_right_mean, FinDist.expect_const, sub_zero]

/-- All changes of correlation preserve a payoff exactly when it is a sum
of one-coordinate payoffs. No finiteness assumption on the carriers is needed. -/
theorem preserves_marginals_iff_additive [Nonempty First] [Nonempty Second]
    (payoff : First × Second → ℝ) :
    (∀ first second : FinDist (First × Second),
      first.map Prod.fst = second.map Prod.fst →
      first.map Prod.snd = second.map Prod.snd →
      first.expect payoff = second.expect payoff) ↔
      ∃ row : First → ℝ, ∃ column : Second → ℝ,
        ∀ outcome, payoff outcome = row outcome.1 + column outcome.2 := by
  constructor
  · intro preserves
    let rowBase : First := Classical.ofNonempty
    let columnBase : Second := Classical.ofNonempty
    refine ⟨fun row => payoff (row, columnBase),
      fun col => payoff (rowBase, col) - payoff (rowBase, columnBase), ?_⟩
    rintro ⟨row, col⟩
    let diagonal := FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure (row, col)) (FinDist.pure (rowBase, columnBase))
    let crossed := FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure (row, columnBase)) (FinDist.pure (rowBase, col))
    have left : diagonal.map Prod.fst = crossed.map Prod.fst := by
      simp [diagonal, crossed, FinDist.map_mix]
    have right : diagonal.map Prod.snd = crossed.map Prod.snd := by
      simp only [diagonal, crossed, FinDist.map_mix, FinDist.map_pure]
      apply FinDist.ext_of_prob
      intro value
      simp only [FinDist.prob_mix]
      ring
    have equal := preserves diagonal crossed left right
    simp only [diagonal, crossed, FinDist.expect_mix, FinDist.expect_pure] at equal
    linarith
  · rintro ⟨row, column, representation⟩ first second left right
    have same : payoff = fun outcome => row outcome.1 + column outcome.2 :=
      funext representation
    rw [same]
    exact expect_additive_eq first second left right row column

end GameTheory.CorrelationPayoff
