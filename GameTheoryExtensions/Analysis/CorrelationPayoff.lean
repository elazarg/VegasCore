/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

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
def interaction (left : PMF First) (right : PMF Second)
    (payoff : First × Second → ℝ) (outcome : First × Second) : ℝ :=
  payoff outcome - expect right (fun second => payoff (outcome.1, second)) -
    expect left (fun first => payoff (first, outcome.2)) +
    expect left (fun first => expect right (fun second => payoff (first, second)))

theorem expect_additive_eq (first second : PMF (First × Second))
    (left : first.map Prod.fst = second.map Prod.fst)
    (right : first.map Prod.snd = second.map Prod.snd)
    (row : First → ℝ) (column : Second → ℝ) :
    expect first (fun outcome => row outcome.1 + column outcome.2) =
      expect second (fun outcome => row outcome.1 + column outcome.2) := by
  have rowEq := congrArg (fun law : PMF First => expect law row) left
  have columnEq := congrArg (fun law : PMF Second => expect law column) right
  simp only [expect_map] at rowEq columnEq
  simp only [FinDist.expect_add, rowEq, columnEq]

/-- For unchanged marginals, only the interaction component contributes to
the expectation difference. The reference laws may be chosen independently. -/
theorem expectation_difference_eq_interaction
    (first second : PMF (First × Second))
    (left : first.map Prod.fst = second.map Prod.fst)
    (right : first.map Prod.snd = second.map Prod.snd)
    (referenceLeft : PMF First) (referenceRight : PMF Second)
    (payoff : First × Second → ℝ) :
    expect first payoff - expect second payoff =
      expect first (interaction referenceLeft referenceRight payoff) -
        expect second (interaction referenceLeft referenceRight payoff) := by
  have rowEq := congrArg (fun law : PMF First => expect law
    (fun row => expect referenceRight (fun col => payoff (row, col)))) left
  have columnEq := congrArg (fun law : PMF Second => expect law
    (fun col => expect referenceLeft (fun row => payoff (row, col)))) right
  simp only [expect_map] at rowEq columnEq
  unfold interaction
  simp only [FinDist.expect_add, FinDist.expect_sub, expect_constant]
  rw [rowEq, columnEq]
  ring

/-- A centered interaction has zero mean on each coordinate of the product
reference distribution. This gives the ordinary two-factor payoff decomposition. -/
theorem interaction_right_mean (left : PMF First) (right : PMF Second)
    (payoff : First × Second → ℝ) (row : First) :
    expect right (fun col => interaction left right payoff (row, col)) = 0 := by
  simp only [interaction, FinDist.expect_add, FinDist.expect_sub, expect_constant]
  rw [FinDist.expect_comm right left]
  ring

theorem interaction_left_mean (left : PMF First) (right : PMF Second)
    (payoff : First × Second → ℝ) (col : Second) :
    expect left (fun row => interaction left right payoff (row, col)) = 0 := by
  simp only [interaction, FinDist.expect_add, FinDist.expect_sub, expect_constant]
  ring

/-- The gain or loss from the actual coupling, relative to the product
distribution with exactly the same marginals, is the mean interaction payoff. -/
theorem correlation_gain_eq_interaction (law : PMF (First × Second))
    (payoff : First × Second → ℝ) :
    expect law payoff -
        expect (bindPairLaw (law.map Prod.fst) (fun _ => (law.map Prod.snd))) payoff =
      expect law (interaction (law.map Prod.fst) (law.map Prod.snd) payoff) := by
  rw [expectation_difference_eq_interaction law _
    (bindPairLaw_map_fst _ _).symm (FinDist.map_snd_product _ _).symm
    (law.map Prod.fst) (law.map Prod.snd), FinDist.expect_product]
  simp only [interaction_right_mean, expect_constant, sub_zero]

/-- All changes of correlation preserve a payoff exactly when it is a sum
of one-coordinate payoffs. No finiteness assumption on the carriers is needed. -/
theorem preserves_marginals_iff_additive [Nonempty First] [Nonempty Second]
    (payoff : First × Second → ℝ) :
    (∀ first second : PMF (First × Second),
      first.map Prod.fst = second.map Prod.fst →
      first.map Prod.snd = second.map Prod.snd →
      expect first payoff = expect second payoff) ↔
      ∃ row : First → ℝ, ∃ column : Second → ℝ,
        ∀ outcome, payoff outcome = row outcome.1 + column outcome.2 := by
  constructor
  · intro preserves
    let rowBase : First := Classical.ofNonempty
    let columnBase : Second := Classical.ofNonempty
    refine ⟨fun row => payoff (row, columnBase),
      fun col => payoff (rowBase, col) - payoff (rowBase, columnBase), ?_⟩
    rintro ⟨row, col⟩
    let diagonal := mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (row, col)) (PMF.pure (rowBase, columnBase))
    let crossed := mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (row, columnBase)) (PMF.pure (rowBase, col))
    have left : diagonal.map Prod.fst = crossed.map Prod.fst := by
      simp [diagonal, crossed, mix_map]
    have right : diagonal.map Prod.snd = crossed.map Prod.snd := by
      simp only [diagonal, crossed, mix_map, PMF.pure_map]
      apply pmf_ext_toReal
      intro value
      simp only [mix_apply_toReal]
      ring
    have equal := preserves diagonal crossed left right
    simp only [diagonal, crossed, FinDist.expect_mix, expect_pure] at equal
    linarith
  · rintro ⟨row, column, representation⟩ first second left right
    have same : payoff = fun outcome => row outcome.1 + column outcome.2 :=
      funext representation
    rw [same]
    exact expect_additive_eq first second left right row column

end GameTheory.CorrelationPayoff
